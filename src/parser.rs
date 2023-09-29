use sqlparser::{
    ast::{Expr, Statement, Value},
    dialect::{Dialect, SQLiteDialect},
    keywords::Keyword,
    parser::{Parser, ParserError},
    tokenizer::Token,
};

#[derive(Debug)]
/// Custom dialect based on SQLITE that accepts IF NOT EXISTS on CREATE VIEW
pub struct CreateViewIfNotExistsDialect {
    inner_dialect: SQLiteDialect,
}

impl Dialect for CreateViewIfNotExistsDialect {
    fn is_identifier_start(&self, ch: char) -> bool {
        self.inner_dialect.is_identifier_part(ch)
    }

    fn is_identifier_part(&self, ch: char) -> bool {
        self.inner_dialect.is_identifier_part(ch)
    }

    fn supports_group_by_expr(&self) -> bool {
        self.inner_dialect.supports_group_by_expr()
    }

    fn parse_statement(&self, parser: &mut Parser) -> Option<Result<Statement, ParserError>> {
        let next_token = parser.next_token();
        match &next_token.token {
            Token::Word(w) => match w.keyword {
                Keyword::CREATE => {
                    if parser.parse_keyword(Keyword::VIEW) {
                        parser.prev_token();
                        return Some(CreateViewIfNotExistsDialect::parse_create_view(
                            parser, false,
                        ));
                    }

                    parser.prev_token();
                    return None;
                }
                Keyword::NoKeyword => {
                    if w.value != "PRAGMA" {
                        parser.prev_token();
                        return None;
                    }

                    loop {
                        let token = parser.next_token();
                        match &token.token {
                            Token::SemiColon => {
                                parser.prev_token();
                                // Return a no-op statement like ASSERT true;
                                return Some(Ok(Statement::Assert {
                                    condition: Expr::Value(Value::Boolean(true)),
                                    message: None,
                                }));
                            }
                            _ => {
                                continue;
                            }
                        }
                    }
                }
                _ => {
                    parser.prev_token();
                    return None;
                }
            },
            _ => {
                parser.prev_token();
                return None;
            }
        }
    }
}

impl CreateViewIfNotExistsDialect {
    pub fn new() -> Self {
        Self {
            inner_dialect: SQLiteDialect {},
        }
    }

    pub fn parse_create_view(
        parser: &mut Parser,
        or_replace: bool,
    ) -> Result<Statement, ParserError> {
        let materialized = parser.parse_keyword(Keyword::MATERIALIZED);
        parser.expect_keyword(Keyword::VIEW)?;

        // This part is the special part from this Dialect, where we skip over IF, NOT and EXISTS
        let if_not_exists = parser.parse_keyword(Keyword::IF);
        if if_not_exists {
            parser.expect_keyword(Keyword::NOT)?;
            parser.expect_keyword(Keyword::EXISTS)?;
        }

        let name = parser.parse_object_name()?;
        let columns = parser
            .parse_parenthesized_column_list(sqlparser::parser::IsOptional::Optional, false)?;
        let with_options = parser.parse_options(Keyword::WITH)?;

        let cluster_by = if parser.parse_keyword(Keyword::CLUSTER) {
            parser.expect_keyword(Keyword::BY)?;
            parser
                .parse_parenthesized_column_list(sqlparser::parser::IsOptional::Optional, false)?
        } else {
            vec![]
        };

        parser.expect_keyword(Keyword::AS)?;
        let query = Box::new(parser.parse_query()?);
        // Optional `WITH [ CASCADED | LOCAL ] CHECK OPTION` is widely supported here.
        Ok(Statement::CreateView {
            name,
            columns,
            query,
            materialized,
            or_replace,
            with_options,
            cluster_by,
        })
    }
}
