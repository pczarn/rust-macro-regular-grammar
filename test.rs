#![feature(phase)]

#[phase(syntax)]
extern crate macro_parser;

fn main() {
    assert!(
        matches!(([a]) [a])
    );

    assert!(
        matches!((a b) a b)
    );

    assert!(
        matches!(($e:expr) ident)
    );

    assert!(
        matches!(($(1 2)+ 1) 1 2 1)
    );

    assert!(
        !matches!(($(1)+) 2)
    );

    assert!(
        matches!((a $(x $x:ident)+) a x z x yyy)
    );

    // matches!((a $([x $x:ident])+) a [x z] [x yyy]);

    assert!(
        matches!(
            ($BitFlags:ident: $T:ty
                $($Flag:ident $(= $value:expr)*),*
            )

            Flags: uint
                A = 1,
                B = 2
        )
    );
}
