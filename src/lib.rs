//! Parses and validates EAN-13 barcodes and their subset UPC-A
//!
//! # Examples
//!
//! ```rust
//! use ean13::Ean13;
//!
//! fn main() {
//!     let sample = Ean13::from_str("0010576000465").unwrap();
//!     assert_eq!(sample.to_string(), "0010576000465".to_string());
//!     
//!     // 12 digit codes are assumed to be UPC-A, and the implied 0 is inserted at the start automatically
//!     let upca_sample = Ean13::from_str("010576000465").unwrap();
//!     assert_eq!(upca_sample.to_string(), "0010576000465".to_string());
//!
//!     assert_eq!(Ean13::from_str("010576000466"), Err(ean13::Error::InvalidCheckDigit));
//! }
//! ```

use std::{fmt, str::FromStr};

use serde::{Deserialize, Serialize};

/// Calculates the check digit for an EAN13 based on the first 12 digits of the code. Useful for
/// validating codes
///
/// # Arguments
///
/// * `first_12` - The first 12 digits of the code to calculate a check digit for
///
/// # Returns
///
/// The appropriate check digit for the supplied code
pub fn calculate_check_digit(first_12: [u8; 12]) -> u8 {
    let sum_odd: u32 = first_12.iter().step_by(2).map(|&d| d as u32).sum();
    let sum_even: u32 = first_12.iter().skip(1).step_by(2).map(|&d| d as u32).sum();
    let total = sum_even * 3 + sum_odd;
    let mut check = total % 10;
    if check != 0 {
        check = 10 - check;
    }
    check as u8
}

/// Errors that occur when validating a code
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// Occurs when a code is not exactly 13 digits long. (Or 12 digits as a preceding 0 is assumed)
    InvalidLength,

    /// There is a character in the code that is not 0-9
    InvalidDigit,

    /// The check digit of the supplied code is incorrect
    InvalidCheckDigit,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for Error {}

/// Represents a validated EAN-13 barcode
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ean13 {
    digits: [u8; 13],
}

impl Ean13 {
    /// Attempts to parse &str into an EAN-13
    ///
    /// # Arguments
    ///
    /// * `input` - The string that represents the code to validate
    ///
    /// # Returns
    ///
    /// * A valid [`Ean13`] if successful. Otherwise, return an [`Error`]
    ///
    /// # Errors
    ///
    /// Returns a member of [`Error`] if the supplied code is not 12 or 13 digits long, if
    /// there are any characters other than 0-9 in the code, or if the supplied check digit is
    /// incorrect
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ean13::Ean13;
    ///
    /// let valid = Ean13::from_str("706285102001").unwrap();
    /// assert_eq!(valid.to_string(), "0706285102001".to_string());
    /// ```
    pub fn from_str(input: &str) -> Result<Self, Error> {
        let normalized = match input.len() {
            // Handle UPC-A input by padding with the implied 0
            12 => format!("0{}", input),
            13 => input.to_string(),
            _ => return Err(Error::InvalidLength),
        };

        let mut digits = [0u8; 13];
        for (i, ch) in normalized.chars().enumerate() {
            digits[i] = ch
                .to_digit(10)
                .ok_or(Error::InvalidDigit)?
                .try_into()
                .or(Err(Error::InvalidDigit))?;
        }

        // Validate check digit
        let first_12: [u8; 12] = digits[0..12].try_into().or(Err(Error::InvalidLength))?;
        let expected = calculate_check_digit(first_12);
        let actual = digits[12];
        if expected != actual {
            return Err(Error::InvalidCheckDigit);
        }

        Ok(Self { digits })
    }

    /// WARNING: If used incorrectly, it is very likely this function will create valid looking [`Ean13`]s
    /// that are actually completely divorced from the correct code. Whenever possible, prefer to use
    /// [`Ean13::from_str`].
    ///
    /// Attempt to create [`Ean13`] from a string that may be malformed. This includes removing all
    /// non-numeric characters, '0' padding the start of the string to match exactly 13 characters
    /// in length, and correcting the check digit, if it is incorrect.
    ///
    /// If the string still cannot be converted into an [`Ean13`], return the corresponding [`Error`]
    ///
    /// # Arguments
    ///
    /// * `broken_str` - The string to attempt to convert into an [`Ean13`]. May contain
    /// non-numeric characters, be of a bad length, or have an incorrect check digit.
    ///
    /// # Returns
    ///
    /// If any existing malformations of the string can be fixed (too short, bad check digit, or
    /// containing non-numeric characters), then return the corresponding [`Ean13`]. Otherwise,
    /// return the appropriate [`Error`]
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ean13::Ean13;
    ///
    /// // All non-numeric characters are ignored
    /// assert_eq!(
    ///     Ean13::from_str_nonstrict("a761458256240").unwrap(),
    ///     Ean13::from_str("0761458256240").unwrap()
    /// );
    ///
    /// // Codes shorter than 13 digits will be forward padded with zeros until their length is 13
    /// assert_eq!(
    ///     Ean13::from_str_nonstrict("1234565").unwrap(),
    ///     Ean13::from_str("0000001234565").unwrap()
    /// );
    ///
    /// // Codes longer than 13 characters without any preceeding zeros will still fail to generate
    /// assert_eq!(
    ///     Ean13::from_str_nonstrict("12345678901234"),
    ///     Err(ean13::Error::InvalidLength)
    /// );
    ///
    /// // Codes longer than 13 digits with preceeding zeros will have preceeding zeros truncated
    /// assert_eq!(
    ///     Ean13::from_str_nonstrict("00000000001234565").unwrap(),
    ///     Ean13::from_str("0000001234565").unwrap()
    /// );
    ///
    /// // Codes with an incorrect check digit will have their check digit fixed
    /// assert_eq!(
    ///     Ean13::from_str_nonstrict("0000001234566").unwrap(),
    ///     Ean13::from_str("0000001234565").unwrap()
    /// );
    ///
    /// // Be very careful! Strings that are not close to barcodes at all may still result in valid
    /// // looking [`Ean13`]s
    /// assert_eq!(
    ///     Ean13::from_str_nonstrict("absolute nonsense").unwrap(),
    ///     Ean13::from_str("0000000000000").unwrap()
    /// );
    /// ```
    pub fn from_str_nonstrict(broken_str: &str) -> Result<Ean13, Error> {
        let only_digits: String = broken_str.chars().filter(|c| c.is_digit(10)).collect();
        let normalized = format!("{:0>13}", only_digits.trim_start_matches("0"));
        let mut digit_vec: Vec<u8> = normalized
            .chars()
            .filter_map(|c| c.to_digit(10))
            .map(|d| d as u8)
            .collect();
        if digit_vec.len() != 13 {
            return Err(Error::InvalidLength);
        }
        if let None = digit_vec.pop() {
            return Err(Error::InvalidLength);
        }
        let first_12: [u8; 12] = digit_vec.try_into().or(Err(Error::InvalidLength))?;
        let check_digit = calculate_check_digit(first_12);
        let mut digit_vec: Vec<u8> = first_12.into();
        digit_vec.push(check_digit);
        Ok(Ean13::from_str(
            &digit_vec.iter().map(|d| d.to_string()).collect::<String>(),
        )?)
    }

    pub fn to_string(&self) -> String {
        self.digits.iter().map(|d| d.to_string()).collect()
    }

    /// Represents the code as an array of 13 u8 digits
    pub fn as_arr(&self) -> [u8; 13] {
        self.digits.clone()
    }
}

impl fmt::Display for Ean13 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "EAN-13({})", self.to_string())
    }
}

impl FromStr for Ean13 {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_str(s)
    }
}

impl Serialize for Ean13 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

impl<'de> Deserialize<'de> for Ean13 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        Ean13::from_str(&s).map_err(serde::de::Error::custom)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Ean13, Error};

    #[test]
    fn test_serialize() {
        let upc = Ean13::from_str("041303015070").unwrap();
        let json = serde_json::json!({"upc": upc});
        assert_eq!(json.to_string(), r#"{"upc":"0041303015070"}"#);
    }

    #[test]
    fn test_deserialize() {
        let deserialized: Ean13 = serde_json::from_str("\"041303015070\"").unwrap();
        assert_eq!(deserialized, Ean13::from_str("041303015070").unwrap());
    }

    #[test]
    fn test_display() {
        assert_eq!(
            format!("{}", Ean13::from_str("041303015070").unwrap()),
            "EAN-13(0041303015070)"
        );
    }

    #[test]
    fn test_to_string() {
        assert_eq!(
            Ean13::from_str("0041303015070").unwrap().to_string(),
            "0041303015070".to_string()
        );
    }

    #[test]
    fn test_calculate_check_digit() {
        let valids = [
            ("004130301507", 0u8),
            ("007797509512", 6),
            ("073803920906", 3),
            ("001410005297", 5),
            ("080882908146", 6),
            ("080812411166", 0),
            ("999999999999", 4),
        ];

        for (upc, check) in valids {
            let first_12: [u8; 12] = upc
                .chars()
                .map(|c| c.to_digit(10).unwrap() as u8)
                .collect::<Vec<u8>>()
                .try_into()
                .unwrap();
            assert_eq!(crate::calculate_check_digit(first_12), check);
        }
    }

    #[test]
    fn test_from_str() {
        assert_eq!(Ean13::from_str(""), Err(Error::InvalidLength));
        assert_eq!(
            Ean13::from_str("041303015071"),
            Err(Error::InvalidCheckDigit)
        );
        assert_eq!(
            Ean13::from_str("0041303015071"),
            Err(Error::InvalidCheckDigit)
        );
        assert_eq!(Ean13::from_str("00413b3015071"), Err(Error::InvalidDigit));
    }

    #[test]
    fn test_from_str_nonstrict() {
        // All non-numeric characters are ignored
        assert_eq!(
            Ean13::from_str_nonstrict("a761458256240").unwrap(),
            Ean13::from_str("0761458256240").unwrap()
        );

        // Codes shorter than 13 digits will be forward padded with zeros until their length is 13
        assert_eq!(
            Ean13::from_str_nonstrict("1234565").unwrap(),
            Ean13::from_str("0000001234565").unwrap()
        );

        // Codes longer than 13 characters without any preceeding zeros will still fail to generate
        assert_eq!(
            Ean13::from_str_nonstrict("12345678901234"),
            Err(Error::InvalidLength)
        );

        // Codes longer than 13 digits with preceeding zeros will have preceeding zeros truncated
        assert_eq!(
            Ean13::from_str_nonstrict("00000000001234565").unwrap(),
            Ean13::from_str("0000001234565").unwrap()
        );

        // Codes with an incorrect check digit will have their check digit fixed
        assert_eq!(
            Ean13::from_str_nonstrict("0000001234566").unwrap(),
            Ean13::from_str("0000001234565").unwrap()
        );

        // Be very careful! Strings that are not close to barcodes at all may still result in valid
        // looking [`Ean13`]s
        assert_eq!(
            Ean13::from_str_nonstrict("absolute nonsense").unwrap(),
            Ean13::from_str("0000000000000").unwrap()
        );
    }

    #[test]
    fn test_as_arr() {
        assert_eq!(
            Ean13::from_str("706285102001").unwrap().as_arr(),
            [0, 7, 0, 6, 2, 8, 5, 1, 0, 2, 0, 0, 1]
        );
    }
}
