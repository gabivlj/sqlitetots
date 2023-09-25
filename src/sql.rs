use anyhow::Context;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use sqlparser::ast::{
    AlterTableOperation, ColumnDef, ColumnOption, ColumnOptionDef, DataType, ObjectName,
    ObjectType, Statement,
};
use sqlparser::dialect::SQLiteDialect;
use sqlparser::parser::Parser;

#[derive(Copy, Clone)]
pub enum SqliteType {
    Integer,
    Text,
    Boolean,
}

struct Column {
    name: DefaultSymbol,
    sql_type: SqliteType,
    nullable: bool,
}

type ColumnList = SmallVec<[Column; 16]>;

struct Columns<'a> {
    columns: ColumnList,
    last_decl_statement: &'a Statement,
    kind: ColumnsKind,
}

enum ColumnsKind {
    View,
    Table,
}

pub fn generate_typescript_types(sql: &str) -> Result<(), GeneratorError> {
    let ast = Parser::parse_sql(&SQLiteDialect {}, sql).context("parsing sql")?;
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
        println!("let {} = eg.object({{", self.strings.resolve(name).unwrap());
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
        }

        return false;
    }

    fn intern_symbol(&mut self, name: &ObjectName) -> Result<DefaultSymbol, GeneratorError> {
        Ok(self.strings.get_or_intern(
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
            nullable: Generator::non_nullable(&column.options),
        })
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
            Statement::CreateView { name, .. } => {
                println!("it's a create table! I guess :- ): {name}");
                Err(GeneratorError::Unimplemented("create view"))?;
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
                let mut column = self.tables.get_mut(&name).ok_or_else(|| {
                    GeneratorError::TableNotExist(String::from(self.strings.resolve(name).unwrap()))
                })?;
                if let ColumnsKind::View = column.kind {
                    return Err(GeneratorError::IsNotATable(String::from(
                        self.strings.resolve(name).unwrap(),
                    )));
                }

                Generator::handle_alter_table_ops(&mut column, &mut self.strings, &operations)?;
            }

            _ => {}
        }

        Ok(())
    }
}
