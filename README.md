
# moss

## Usage

Using moss requires the `nightly` toolchain.

**Build:**

```
cargo build
```

**Run:**

```
cargo run -- --sysroot ~/.multirust/toolchains/nightly <target.rs>

#Alternativly
target/debug/mossc --sysroot ~/.multirust/toolchains/nightly <target.rs>
```

## About

Moss is an experimental bytecode interpreter for rust.


### Differences to Rust

For simplification moss only uses two kinds of integers: 64bit unsigned and 64 bit signed.



