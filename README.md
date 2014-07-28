## Macro By Example with a Pike VM for Rust

The idea is that every macro definition also defines a regular language.

### Example

```rust
matches!(
    ($enum:ident: $T:ty
        $($variant:ident $(= $value:expr)*)+
    )

    Flags: uint
        A = 1
        B = 2
        C = 3
)
// => true
```

### TODO

* capture nonterminals.
* count sequence repetitons.
* write `macro_rules!`
