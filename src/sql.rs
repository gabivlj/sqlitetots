use anyhow::Context;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use sqlparser::ast::{
    AlterTableOperation, ColumnDef, ColumnOption, ColumnOptionDef, DataType, Expr, Join,
    ObjectName, ObjectType, SelectItem, SetExpr, Statement, Table, TableAlias, TableFactor,
    TableWithJoins, Value,
};
use sqlparser::parser::Parser;

#[derive(Copy, Clone, Debug)]
pub enum SqliteType {
    Integer,
    Text,
    Boolean,
}

#[derive(Debug, Clone)]
struct Column {
    name: DefaultSymbol,
    sql_type: SqliteType,
    nullable: bool,
}

type ColumnList = SmallVec<[Column; 16]>;

#[derive(Debug)]
struct Columns<'a> {
    columns: ColumnList,
    last_decl_statement: &'a Statement,
    kind: ColumnsKind,
}

#[derive(Debug)]
enum ColumnsKind {
    View,
    Table,
}

pub fn generate_typescript_types(sql: &str) -> Result<(), GeneratorError> {
    let dialect = parser::CreateViewIfNotExistsDialect::new();
    let ast = Parser::parse_sql(&dialect, sql).context("parsing sql")?;
    let mut generator = Generator::new();
    let result = generator.process_sql_statements(&ast);
    // generate anyway
    generator.generate();
    result.context("processing sql statements")?;
    return Ok(());
}

type ColumnTable<'a> = FxHashMap<DefaultSymbol, Columns<'a>>;

struct Generator<'a> {
    strings: StringInterner,
    tables: ColumnTable<'a>,
}

use string_interner::{DefaultSymbol, StringInterner};
use thiserror::Error;

use crate::parser;

#[derive(Debug)]
pub struct MultipleGeneratorErrors(Vec<GeneratorError>);

impl std::fmt::Display for MultipleGeneratorErrors {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, item) in self.0.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }

            let _ = write!(f, "\t{}. {}", i + 1, item)?;
        }

        Ok(())
    }
}

#[derive(Error, Debug)]
pub enum GeneratorError {
    #[error("multiple:\n{0}")]
    Multiple(MultipleGeneratorErrors),

    #[error("in statement number {index} `{statement}`: {inner}")]
    Statement {
        index: usize,
        statement: Statement,
        inner: Box<GeneratorError>,
    },

    #[error("unimplemented {0}")]
    Unimplemented(&'static str),

    #[error("unknown internal error")]
    Unknown(#[from] anyhow::Error),

    #[error("unknown sql data type '{0}'")]
    UnknownSqlDataType(DataType),

    #[error("{0}")]
    Base(&'static str),

    #[error("table '{0}' doesn't exist")]
    TableNotExist(String),

    #[error("view '{0}' doesn't exist")]
    ViewNotExist(String),

    #[error("'{0}' is not a table")]
    IsNotATable(String),

    #[error("column '{0}' doesn't exist")]
    ColumnNotExist(String),

    #[error("ambiguous reference {0}, expected <table_name>.{0}")]
    AmbiguousReference(String),
}

impl<'a> Generator<'a> {
    fn new() -> Self {
        Self {
            strings: string_interner::StringInterner::default(),
            tables: FxHashMap::default(),
        }
    }

    fn type_to_ts(sql_type: SqliteType) -> &'static str {
        match sql_type {
            SqliteType::Boolean => "boolean",
            SqliteType::Integer => "number",
            SqliteType::Text => "string",
        }
    }

    fn optional(optional: bool) -> &'static str {
        if optional {
            return ".optional";
        }

        return "";
    }

    fn generate_col(&self, name: DefaultSymbol, columns: &Columns) {
        println!(
            "const {} = eg.object({{",
            self.strings.resolve(name).unwrap()
        );
        for (i, column) in columns.columns.iter().enumerate() {
            if i > 0 {
                println!();
            }

            print!(
                "  {}: eg.{}{},",
                self.strings.resolve(column.name).unwrap(),
                Generator::type_to_ts(column.sql_type),
                Generator::optional(column.nullable),
            );
        }
        println!("\n}});");
    }

    fn generate(&self) {
        for (key, val) in self.tables.iter() {
            self.generate_col(*key, val);
            println!();
        }
    }

    fn process_sql_statements(
        &mut self,
        statements: &'a [Statement],
    ) -> Result<(), GeneratorError> {
        let mut errors = Vec::with_capacity(statements.len());
        for (i, statement) in statements.iter().enumerate() {
            if let Err(err) = self.process_sql_statement(statement) {
                errors.push(GeneratorError::Statement {
                    index: i + 1,
                    statement: statement.clone(),
                    inner: Box::new(err),
                });
            }
        }

        if errors.len() > 0 {
            return Err(GeneratorError::Multiple(MultipleGeneratorErrors(errors)));
        }

        Ok(())
    }

    fn handle_alter_table_ops<'b, 'c>(
        columns: &'b mut Columns,
        strings: &'c mut StringInterner,
        ops: &[AlterTableOperation],
    ) -> Result<(), GeneratorError> {
        for op in ops {
            Generator::handle_alter_table_op(columns, strings, op)?;
        }

        Ok(())
    }

    fn handle_alter_table_op(
        columns: &mut Columns,
        strings: &mut StringInterner,
        op: &AlterTableOperation,
    ) -> Result<(), GeneratorError> {
        match op {
            AlterTableOperation::AddColumn { column_def, .. } => columns
                .columns
                .push(Generator::column_def_to_sqlite_column(strings, column_def)?),
            AlterTableOperation::RenameColumn {
                old_column_name,
                new_column_name,
            } => {
                let old_name = strings.get_or_intern(&old_column_name.value);
                let new_name = strings.get_or_intern(&new_column_name.value);
                for column in &mut columns.columns {
                    if column.name == old_name {
                        column.name = new_name;
                        return Ok(());
                    }
                }

                return Err(GeneratorError::ColumnNotExist(String::from(
                    strings.resolve(old_name).expect("for sure... right?"),
                )));
            }
            AlterTableOperation::DropColumn { column_name, .. } => {
                let name = strings.get_or_intern(&column_name.value);
                let mut index = -1;
                for (idx, column) in &mut columns.columns.iter_mut().enumerate() {
                    if column.name == name {
                        index = idx as isize;
                        break;
                    }
                }

                if index == -1 {
                    return Err(GeneratorError::ColumnNotExist(String::from(
                        strings.resolve(name).expect("for sure... right?"),
                    )));
                }

                columns.columns.swap_remove(index as usize);
            }
            _ => Err(GeneratorError::Unimplemented(
                "unimplemented this kind of ALTER TABLE operation",
            ))?,
        }

        Ok(())
    }

    fn get_sqlite_type_from_sql_type(t: &DataType) -> Result<SqliteType, GeneratorError> {
        match t {
            DataType::Text
            | DataType::Blob(_)
            | DataType::Varchar(_)
            | DataType::Char(_)
            | DataType::CharVarying(_)
            | DataType::CharacterVarying(_) => Ok(SqliteType::Text),
            DataType::Bool | DataType::Boolean => Ok(SqliteType::Boolean),
            // so everything has always been an integer?
            // yes.
            DataType::Int(_)
            | DataType::Integer(_)
            | DataType::Int2(_)
            | DataType::Int4(_)
            | DataType::Real
            | DataType::Float(_)
            | DataType::Float4
            | DataType::UnsignedBigInt(_)
            | DataType::UnsignedInt(_)
            | DataType::UnsignedInt2(_)
            | DataType::UnsignedInt4(_)
            | DataType::UnsignedInt8(_)
            | DataType::UnsignedInteger(_)
            | DataType::UnsignedMediumInt(_)
            | DataType::UnsignedSmallInt(_)
            | DataType::UnsignedTinyInt(_)
            | DataType::TinyInt(_)
            | DataType::Float8
            | DataType::BigInt(_)
            | DataType::BigDecimal(_)
            | DataType::BigNumeric(_) => Ok(SqliteType::Integer),
            _ => Err(GeneratorError::UnknownSqlDataType(t.clone())),
        }
    }

    fn non_nullable(options: &[ColumnOptionDef]) -> bool {
        for option in options {
            if let ColumnOption::NotNull = option.option {
                return true;
            }

            // Handle the case where there is a default
            if let ColumnOption::Default(expr) = &option.option {
                if let Expr::Value(value) = expr {
                    // if the defualt is null, let's keep finding options
                    if let Value::Null = value {
                        continue;
                    }
                }

                return true;
            }

            if let ColumnOption::Unique { is_primary } = &option.option {
                // technically, primary should allow for null,
                // however 99% of definitions of PRIMARY assume that insertions fill it with a
                // value
                if *is_primary {
                    return true;
                }

                // unique value should have not null constraint
                continue;
            }
        }

        return false;
    }

    fn intern_symbol(&mut self, name: &ObjectName) -> Result<DefaultSymbol, GeneratorError> {
        Generator::intern_symbol_from_internet(&mut self.strings, name)
    }

    fn intern_symbol_from_internet(
        interner: &mut StringInterner,
        name: &ObjectName,
    ) -> Result<DefaultSymbol, GeneratorError> {
        Ok(interner.get_or_intern(
            &(name.0.last().ok_or(GeneratorError::Base(
                "unexpected table name doesn't have elements",
            ))?)
            .value,
        ))
    }

    fn column_def_to_sqlite_column(
        strings: &mut StringInterner,
        column: &ColumnDef,
    ) -> Result<Column, GeneratorError> {
        let t = Generator::get_sqlite_type_from_sql_type(&column.data_type)?;
        let name = strings.get_or_intern(&column.name.value);
        Ok(Column {
            name,
            sql_type: t,
            nullable: !Generator::non_nullable(&column.options),
        })
    }

    fn assert_table_exists_mut<'b, 'c>(
        tables: &'b mut ColumnTable<'c>,
        strings: &mut StringInterner,
        name: DefaultSymbol,
    ) -> Result<&'b mut Columns<'c>, GeneratorError> {
        let column = tables.get_mut(&name).ok_or_else(|| {
            GeneratorError::TableNotExist(String::from(strings.resolve(name).unwrap()))
        })?;
        if let ColumnsKind::View = column.kind {
            return Err(GeneratorError::IsNotATable(String::from(
                strings.resolve(name).unwrap(),
            )));
        }

        return Ok(column);
    }

    fn assert_table_or_view_exists<'b, 'c>(
        tables: &'b ColumnTable<'c>,
        strings: &StringInterner,
        name: DefaultSymbol,
    ) -> Result<&'b Columns<'c>, GeneratorError> {
        let column = tables.get(&name).ok_or_else(|| {
            GeneratorError::TableNotExist(String::from(strings.resolve(name).unwrap()))
        })?;
        return Ok(column);
    }

    fn get_table_name_from_table_factor<'b, 'c>(
        &'b mut self,
        table: &'c TableFactor,
    ) -> Result<(DefaultSymbol, DefaultSymbol), GeneratorError> {
        if let TableFactor::Table { name, alias, .. } = &table {
            return self.get_table_name_from_table(name, alias);
        }

        return Err(GeneratorError::Base("expected a simple table name in FROM"));
    }

    fn get_table_name_from_table<'b, 'c>(
        &'b mut self,
        name: &'c ObjectName,
        alias: &'c Option<TableAlias>,
    ) -> Result<(DefaultSymbol, DefaultSymbol), GeneratorError> {
        let table_name = self.intern_symbol(name)?;
        let alias_name = if let Some(alias) = alias {
            self.strings.get_or_intern(&alias.name.value)
        } else {
            table_name
        };

        return Ok((table_name, alias_name));
    }

    fn get_table_and_column_name_from_expr(
        expr: &Expr,
        interner: &mut StringInterner,
    ) -> Result<(DefaultSymbol, DefaultSymbol), GeneratorError> {
        match expr {
            Expr::Identifier(identifier) => {
                return Err(GeneratorError::AmbiguousReference(identifier.value.clone()));
            }
            Expr::CompositeAccess { expr, key } => {
                let table = interner.get_or_intern(&key.value);
                if let Expr::Identifier(identifier) = expr.as_ref() {
                    let identifier = interner.get_or_intern(&identifier.value);
                    return Ok((table, identifier));
                } else {
                    return Err(GeneratorError::Base(
                        "on composite access we expect an identifier, not anything else",
                    ));
                }
            }
            Expr::CompoundIdentifier(idents) => {
                if idents.len() == 1 {
                    return Err(GeneratorError::AmbiguousReference(idents[0].value.clone()));
                }

                let column = interner.get_or_intern(
                    &idents
                        .last()
                        .ok_or_else(|| GeneratorError::Base("expected an identifier"))?
                        .value,
                );
                let table = interner.get_or_intern(&idents[idents.len() - 2].value);
                return Ok((table, column));
            }
            _ => {
                println!("ERROR: {:?}", expr);
                return Err(GeneratorError::Base("expected composite access on column"));
            }
        }
    }

    fn process_sql_statement(&mut self, statement: &'a Statement) -> Result<(), GeneratorError> {
        match statement {
            Statement::CreateTable { name, columns, .. } => {
                let mut columns_gen = ColumnList::new();
                for column in columns {
                    columns_gen.push(Generator::column_def_to_sqlite_column(
                        &mut self.strings,
                        column,
                    )?);
                }
                let name = self.intern_symbol(name)?;
                self.tables.insert(
                    name,
                    Columns {
                        columns: columns_gen,
                        last_decl_statement: statement,
                        kind: ColumnsKind::Table,
                    },
                );
            }
            Statement::CreateView { name, query, .. } => {
                let view_name = self.intern_symbol(name)?;
                if let SetExpr::Select(query) = query.as_ref().body.as_ref() {
                    let query_from_first = query
                        .from
                        .first()
                        .ok_or_else(|| GeneratorError::Base("expected FROM table"))?;
                    let names: Result<Vec<(DefaultSymbol, DefaultSymbol)>, GeneratorError> =
                        query_from_first
                            .joins
                            .iter()
                            .map(|el| self.get_table_name_from_table_factor(&el.relation))
                            .collect();
                    let mut names = names?;
                    names.push(self.get_table_name_from_table_factor(&query_from_first.relation)?);
                    let names_result: Result<FxHashMap<DefaultSymbol, &Columns>, GeneratorError> =
                        names.iter().fold(
                            Result::Ok(FxHashMap::default()),
                            |prev, (name, alias)| {
                                let mut prev = prev?;
                                prev.insert(
                                    *alias,
                                    Generator::assert_table_or_view_exists(
                                        &self.tables,
                                        &self.strings,
                                        *name,
                                    )?,
                                );
                                Ok(prev)
                            },
                        );

                    let strings = &mut self.strings;
                    let names = names_result?;
                    let get_table = |strings: &StringInterner, table_name| {
                        names.get(&table_name).ok_or_else(|| {
                            GeneratorError::TableNotExist(
                                strings
                                    .resolve(table_name)
                                    .expect("unreachable")
                                    .to_string(),
                            )
                        })
                    };
                    let mut columns = ColumnList::new();
                    for column in query.as_ref().projection.iter() {
                        match column {
                            SelectItem::ExprWithAlias { expr, alias } => {
                                let column_alias_name = strings.get_or_intern(&alias.value);
                                let (table_name, column_name) =
                                    Generator::get_table_and_column_name_from_expr(expr, strings)?;
                                let table = get_table(strings, table_name)?;
                                let column = table
                                    .columns
                                    .iter()
                                    .find(|column| column.name == column_name)
                                    .ok_or_else(|| {
                                        GeneratorError::ColumnNotExist(
                                            strings
                                                .resolve(column_name)
                                                .expect("unreachable")
                                                .to_string(),
                                        )
                                    })?;
                                // copy the column but with a different name due to alias
                                let column = Column {
                                    name: column_alias_name,
                                    sql_type: column.sql_type,
                                    nullable: column.nullable,
                                };
                                columns.push(column);
                            }

                            SelectItem::QualifiedWildcard(name, _) => {
                                let table_name =
                                    Generator::intern_symbol_from_internet(strings, name)?;
                                let table = get_table(strings, table_name)?;
                                table
                                    .columns
                                    .iter()
                                    .for_each(|column| columns.push(column.clone()));
                            }
                            SelectItem::UnnamedExpr(expr) => {
                                let (table_name, column_name) =
                                    Generator::get_table_and_column_name_from_expr(expr, strings)?;
                                let table = get_table(strings, table_name)?;
                                let column = table
                                    .columns
                                    .iter()
                                    .find(|column| column.name == column_name)
                                    .ok_or_else(|| {
                                        GeneratorError::ColumnNotExist(
                                            strings
                                                .resolve(column_name)
                                                .expect("unreachable")
                                                .to_string(),
                                        )
                                    })?;
                                columns.push(column.clone());
                            }
                            SelectItem::Wildcard(_) => {
                                names.iter().for_each(|(_, table)| {
                                    table
                                        .columns
                                        .iter()
                                        .for_each(|column| columns.push(column.clone()))
                                });
                            }
                        }
                    }

                    self.tables.insert(
                        view_name,
                        Columns {
                            kind: ColumnsKind::View,
                            columns,
                            last_decl_statement: statement,
                        },
                    );
                    return Ok(());
                }

                Err(GeneratorError::Base(
                    "we can't handle other thigs in CREATE VIEW that are not SELECT",
                ))?;
            }
            Statement::Drop {
                object_type, names, ..
            } => match object_type {
                ObjectType::Table => {
                    for name in names {
                        let name = self.intern_symbol(name)?;
                        self.tables.remove(&name).ok_or_else(|| {
                            GeneratorError::TableNotExist(String::from(
                                self.strings.resolve(name).unwrap(),
                            ))
                        })?;
                    }
                }
                ObjectType::View => {
                    for name in names {
                        let name = self.intern_symbol(name)?;
                        self.tables.remove(&name).ok_or_else(|| {
                            GeneratorError::ViewNotExist(String::from(
                                self.strings.resolve(name).unwrap(),
                            ))
                        })?;
                    }
                }

                _ => {}
            },
            Statement::AlterTable {
                name, operations, ..
            } => {
                let name = self.intern_symbol(name)?;
                let column =
                    Generator::assert_table_exists_mut(&mut self.tables, &mut self.strings, name)?;
                Generator::handle_alter_table_ops(column, &mut self.strings, &operations)?;
            }

            _ => {}
        }

        Ok(())
    }
}
