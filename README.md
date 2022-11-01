# fixed_free_list

A fixed-size free-list with optional key lifetime safety and macroless unique typing.
Please consult [**the documentation**](https://docs.rs/fixed_free_list) for more information.

The minimum required Rust version for `fixed_free_list` is 1.63.0. To start using
`fixed_free_list` add the following to your `Cargo.toml`:

```toml
[dependencies]
fixed_free_list = "0.2"
```

For additional performance, enable `unstable` feature on nightly with

```toml
[dependencies]
fixed_free_list = { version = "0.2", features = ["unstable"] }
```

For additional development-time memory safety verification at the cost of performance, enable `strict` feature with

```toml
[dependencies]
fixed_free_list = { version = "0.2", features = ["strict"] }
```

## Example

A short example:

```rust
use fixed_free_list::FixedFreeList;
let mut list: FixedFreeList<i32, 16> = FixedFreeList::new();
let key = list.alloc(8).unwrap();
assert_eq!(unsafe { *list.get_unchecked(key) }, 8);
let value = unsafe { list.get_mut_unchecked(key) };
*value = 2;
assert_eq!(unsafe { list.free_unchecked(key) }, 2);
```

## Safety

This crate uses unsafe code for performance.
It has been extensively fuzz tested with miri to ensure it behaves correctly.

## License

`fixed_free_list` is dual-licensed under either:

* MIT License ([LICENSE-MIT](LICENSE-MIT) or [http://opensource.org/licenses/MIT](http://opensource.org/licenses/MIT))
* Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or [http://www.apache.org/licenses/LICENSE-2.0](http://www.apache.org/licenses/LICENSE-2.0))

at your option.

### Your contributions

Unless you explicitly state otherwise,
any contribution intentionally submitted for inclusion in the work by you,
as defined in the Apache-2.0 license,
shall be dual licensed as above,
without any additional terms or conditions.