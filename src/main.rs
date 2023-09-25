mod sql;

use anyhow::Result;

fn main() -> Result<()> {
    sql::generate_typescript_types(
        "
       CREATE TABLE hello (
         i INTEGER,
         j TEXT
       ); 

       CREATE TABLE hello_2 (
         j TEXT NOT NULL
       ); 

       ALTER TABLE hello_2 ADD COLUMN hello INTEGER;
       --ALTER TABLE hello_3 ADD COLUMN hello INTEGER;
       ALTER TABLE hello_2 ADD COLUMN hellowooor BOOLEAN NOT NULL;
       DROP TABLE hello;

      -- CREATE VIEW HelloViewer AS 
        --    SELECT * FROM hello;
    ",
    )?;
    Ok(())
}
