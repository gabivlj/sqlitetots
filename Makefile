
build:
	cargo build --release

bin/sqlgen: build
	mkdir -p bin
	mv target/release/sqlgen bin/sqlgen