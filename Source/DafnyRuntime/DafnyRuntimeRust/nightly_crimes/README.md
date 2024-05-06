# nightly-crimes

The `nightly_crimes!{}` macro commits horrible crimes to allow you to enable
nightly features on the stable compiler.

https://twitter.com/m_ou_se/status/1410930900116951040

Please do not use this.

## Example

```rust
use nightly_crimes::nightly_crimes;

nightly_crimes! {
    #![feature(never_type)]
    #![feature(box_syntax)]
    fn hey(x: Result<&str, !>) -> Box<String> {
        match x {
            Ok(x) => box x.to_string(),
            Err(x) => x,
        }
    }
}

fn main() {
    println!("{}", hey(Ok("success!")));
}
```

```
$ cargo +stable r
success!
```
