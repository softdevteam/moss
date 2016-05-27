
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



### Stack

The stack is implemented as a vector. We need one continues stack since references into the stack are possible.


#### Memory Model
When normally compiled fixed size variables are stored on the stack. This
includes tuples and structs. Objects which can grow in size (e.g. vectors) have
to be stored on the heap and only a reference (pointer) to the object can be
stored on the stack.

For simplicity we now just store primitive values on the stack. Composed
values are encapsulated into their own wrapper type and just the pointer to it
is stored on the stack.
