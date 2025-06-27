# ean13

Parses and validates EAN-13 barcodes and the UPC-A subset. This crate is intended to be simple and lightweight compared to other barcoding crates. For extra functionality like generating barcode images see [barcoders](https://github.com/buntine/barcoders).

# Examples

```rust
use ean13::{Ean13, Ean13Error};

fn main() {
    let sample = Ean13::from_str("0010576000465").unwrap();
    assert_eq!(sample.to_string(), "0010576000465".to_string());
    
    // 12 digit codes are assumed to be UPC-A, and the implied 0 is inserted at the start automatically
    let upca_sample = Ean13::from_str("010576000465").unwrap();
    assert_eq!(upca_sample.to_string(), "0010576000465".to_string());

    // Attempting to create an invalid EAN-13 will cause an error
    assert_eq!(Ean13::from_str("010576000466"), Err(Ean13Error::InvalidCheckDigit));
}
```

