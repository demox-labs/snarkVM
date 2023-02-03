// Copyright (C) 2019-2022 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

pub mod genesis;
pub use genesis::*;

pub mod powers;
use indexmap::IndexMap;
pub use powers::*;

const REMOTE_URL: &str = "https://testnet3.parameters.aleo.org";


// Degrees
// impl_local!(Degree15, "resources/", "powers-of-beta-15", "usrs");
// impl_remote!(Degree16, REMOTE_URL, "resources/", "powers-of-beta-16", "usrs");
// impl_remote!(Degree17, REMOTE_URL, "resources/", "powers-of-beta-17", "usrs");
// impl_remote!(Degree18, REMOTE_URL, "resources/", "powers-of-beta-18", "usrs");
// impl_remote!(Degree19, REMOTE_URL, "resources/", "powers-of-beta-19", "usrs");
// impl_remote!(Degree20, REMOTE_URL, "resources/", "powers-of-beta-20", "usrs");
// impl_remote!(Degree21, REMOTE_URL, "resources/", "powers-of-beta-21", "usrs");
// impl_remote!(Degree22, REMOTE_URL, "resources/", "powers-of-beta-22", "usrs");
// impl_remote!(Degree23, REMOTE_URL, "resources/", "powers-of-beta-23", "usrs");
// impl_remote!(Degree24, REMOTE_URL, "resources/", "powers-of-beta-24", "usrs");
// impl_remote!(Degree25, REMOTE_URL, "resources/", "powers-of-beta-25", "usrs");
// impl_remote!(Degree26, REMOTE_URL, "resources/", "powers-of-beta-26", "usrs");
// impl_remote!(Degree27, REMOTE_URL, "resources/", "powers-of-beta-27", "usrs");
// impl_remote!(Degree28, REMOTE_URL, "resources/", "powers-of-beta-28", "usrs");

// Shifted Degrees
// impl_local!(ShiftedDegree15, "resources/", "shifted-powers-of-beta-15", "usrs");
// impl_remote!(ShiftedDegree16, REMOTE_URL, "resources/", "shifted-powers-of-beta-16", "usrs");
// impl_remote!(ShiftedDegree17, REMOTE_URL, "resources/", "shifted-powers-of-beta-17", "usrs");
// impl_remote!(ShiftedDegree18, REMOTE_URL, "resources/", "shifted-powers-of-beta-18", "usrs");
// impl_remote!(ShiftedDegree19, REMOTE_URL, "resources/", "shifted-powers-of-beta-19", "usrs");
// impl_remote!(ShiftedDegree20, REMOTE_URL, "resources/", "shifted-powers-of-beta-20", "usrs");
// impl_remote!(ShiftedDegree21, REMOTE_URL, "resources/", "shifted-powers-of-beta-21", "usrs");
// impl_remote!(ShiftedDegree22, REMOTE_URL, "resources/", "shifted-powers-of-beta-22", "usrs");
// impl_remote!(ShiftedDegree23, REMOTE_URL, "resources/", "shifted-powers-of-beta-23", "usrs");
// impl_remote!(ShiftedDegree24, REMOTE_URL, "resources/", "shifted-powers-of-beta-24", "usrs");
// impl_remote!(ShiftedDegree25, REMOTE_URL, "resources/", "shifted-powers-of-beta-25", "usrs");
// impl_remote!(ShiftedDegree26, REMOTE_URL, "resources/", "shifted-powers-of-beta-26", "usrs");
// impl_remote!(ShiftedDegree27, REMOTE_URL, "resources/", "shifted-powers-of-beta-27", "usrs");

// // Powers of Beta Times Gamma * G
// impl_local!(Gamma, "resources/", "powers-of-beta-gamma", "usrs");
// // Negative Powers of Beta in G2
// impl_local!(NegBeta, "resources/", "neg-powers-of-beta", "usrs");
// // Negative Powers of Beta in G2
// impl_local!(BetaH, "resources/", "beta-h", "usrs");

// // Mint
// impl_remote!(MintProver, REMOTE_URL, "resources/", "mint", "prover");
// impl_remote!(MintVerifier, REMOTE_URL, "resources/", "mint", "verifier");
// // Transfer
// impl_remote!(TransferProver, REMOTE_URL, "resources/", "transfer", "prover");
// impl_remote!(TransferVerifier, REMOTE_URL, "resources/", "transfer", "verifier");
// // Join
// impl_remote!(JoinProver, REMOTE_URL, "resources/", "join", "prover");
// impl_remote!(JoinVerifier, REMOTE_URL, "resources/", "join", "verifier");
// // Split
// impl_remote!(SplitProver, REMOTE_URL, "resources/", "split", "prover");
// impl_remote!(SplitVerifier, REMOTE_URL, "resources/", "split", "verifier");
// // Fee
// impl_remote!(FeeProver, REMOTE_URL, "resources/", "fee", "prover");
// impl_remote!(FeeVerifier, REMOTE_URL, "resources/", "fee", "verifier");

use std::sync::Mutex;

lazy_static! {
    pub static ref PARAMETER_PROVIDER: Mutex<IndexMap<String, Vec<u8>>> = {
        let mut map = IndexMap::new();
        // Test
        map.insert("TestProver".into(), Vec::<u8>::new());

        // Powers of Beta
        map.insert("Degree15".into(), Vec::<u8>::new());
        map.insert("Degree16".into(), Vec::<u8>::new());
        map.insert("Degree17".into(), Vec::<u8>::new());
        map.insert("Degree18".into(), Vec::<u8>::new());
        map.insert("Degree19".into(), Vec::<u8>::new());
        map.insert("Degree20".into(), Vec::<u8>::new());
        map.insert("Degree21".into(), Vec::<u8>::new());
        map.insert("Degree22".into(), Vec::<u8>::new());
        map.insert("Degree23".into(), Vec::<u8>::new());
        map.insert("Degree24".into(), Vec::<u8>::new());
        map.insert("Degree25".into(), Vec::<u8>::new());
        map.insert("Degree26".into(), Vec::<u8>::new());
        map.insert("Degree27".into(), Vec::<u8>::new());
        map.insert("Degree28".into(), Vec::<u8>::new());

        // Shifted Powers of Beta
        map.insert("ShiftedDegree15".into(), Vec::<u8>::new());
        map.insert("ShiftedDegree16".into(), Vec::<u8>::new());
        map.insert("ShiftedDegree17".into(), Vec::<u8>::new());
        map.insert("ShiftedDegree18".into(), Vec::<u8>::new());
        map.insert("ShiftedDegree19".into(), Vec::<u8>::new());
        map.insert("ShiftedDegree20".into(), Vec::<u8>::new());
        map.insert("ShiftedDegree21".into(), Vec::<u8>::new());
        map.insert("ShiftedDegree22".into(), Vec::<u8>::new());
        map.insert("ShiftedDegree23".into(), Vec::<u8>::new());
        map.insert("ShiftedDegree24".into(), Vec::<u8>::new());
        map.insert("ShiftedDegree25".into(), Vec::<u8>::new());
        map.insert("ShiftedDegree26".into(), Vec::<u8>::new());
        map.insert("ShiftedDegree27".into(), Vec::<u8>::new());

        // Powers of Beta Times Gamma * G
        map.insert("Gamma".into(), Vec::<u8>::new());
        // Negative Powers of Beta in G2
        map.insert("NegBeta".into(), Vec::<u8>::new());
        // Negative Powers of Beta in G2
        map.insert("BetaH".into(), Vec::<u8>::new());

        // Credits Program
        map.insert("MintProver".into(), Vec::<u8>::new());
        map.insert("MintVerifier".into(), Vec::<u8>::new());
        map.insert("TransferProver".into(), Vec::<u8>::new());
        map.insert("TransferVerifier".into(), Vec::<u8>::new());
        map.insert("JoinProver".into(), Vec::<u8>::new());
        map.insert("JoinVerifier".into(), Vec::<u8>::new());
        map.insert("SplitProver".into(), Vec::<u8>::new());
        map.insert("SplitVerifier".into(), Vec::<u8>::new());
        map.insert("FeeProver".into(), Vec::<u8>::new());
        map.insert("FeeVerifier".into(), Vec::<u8>::new());

        // Inclusion
        map.insert("InclusionProver".into(), Vec::<u8>::new());
        map.insert("InclusionVerifier".into(), Vec::<u8>::new());

        Mutex::new(map)
    };
}

#[macro_export]
macro_rules! impl_web {
    ($name: ident, $fname: tt, $ftype: tt) => {
        use wasm_bindgen::prelude::*;

        pub struct $name;

        #[wasm_bindgen]
        impl $name {
            #[wasm_bindgen(js_namespace = console)]
            pub fn log(s: &str);
        }

        impl $name {
            pub fn load_bytes() -> Result<Vec<u8>, $crate::errors::ParameterError> {
                $name::log(stringify!($name));
                let provider_lock = PARAMETER_PROVIDER.lock();
                match provider_lock {
                    Ok(provider) => {
                        let bytes = provider.get(stringify!($name));
                        assert!(bytes.is_some(), "{} should be defined in the Parameter Provider", stringify!($name));
                        Ok(bytes.unwrap().clone())
                    }
                    Err(_) => {
                        Err(crate::errors::ParameterError::NotFound)
                    }
                }
            }
        }


        paste::item! {
            #[cfg(test)]
            #[test]
            fn [< test_ $fname _ $ftype >]() {
                assert!($name::load_bytes().is_ok());
            }
        }
    };
}

impl_web!(Degree15, "powers-of-beta-15", "powers-of-beta");
impl_web!(Degree16, "powers-of-beta-16", "powers-of-beta");
impl_web!(Degree17, "powers-of-beta-17", "powers-of-beta");
impl_web!(Degree18, "powers-of-beta-18", "powers-of-beta");
impl_web!(Degree19, "powers-of-beta-19", "powers-of-beta");
impl_web!(Degree20, "powers-of-beta-20", "powers-of-beta");
impl_web!(Degree21, "powers-of-beta-21", "powers-of-beta");
impl_web!(Degree22, "powers-of-beta-22", "powers-of-beta");
impl_web!(Degree23, "powers-of-beta-23", "powers-of-beta");
impl_web!(Degree24, "powers-of-beta-24", "powers-of-beta");
impl_web!(Degree25, "powers-of-beta-25", "powers-of-beta");
impl_web!(Degree26, "powers-of-beta-26", "powers-of-beta");
impl_web!(Degree27, "powers-of-beta-27", "powers-of-beta");
impl_web!(Degree28, "powers-of-beta-28", "powers-of-beta");


impl_web!(ShiftedDegree15, "shifted-powers-of-beta-15", "shift-powers-of-beta");
impl_web!(ShiftedDegree16, "shifted-powers-of-beta-16", "shift-powers-of-beta");
impl_web!(ShiftedDegree17, "shifted-powers-of-beta-17", "shift-powers-of-beta");
impl_web!(ShiftedDegree18, "shifted-powers-of-beta-18", "shift-powers-of-beta");
impl_web!(ShiftedDegree19, "shifted-powers-of-beta-19", "shift-powers-of-beta");
impl_web!(ShiftedDegree20, "shifted-powers-of-beta-20", "shift-powers-of-beta");
impl_web!(ShiftedDegree21, "shifted-powers-of-beta-21", "shift-powers-of-beta");
impl_web!(ShiftedDegree22, "shifted-powers-of-beta-22", "shift-powers-of-beta");
impl_web!(ShiftedDegree23, "shifted-powers-of-beta-23", "shift-powers-of-beta");
impl_web!(ShiftedDegree24, "shifted-powers-of-beta-24", "shift-powers-of-beta");
impl_web!(ShiftedDegree25, "shifted-powers-of-beta-25", "shift-powers-of-beta");
impl_web!(ShiftedDegree26, "shifted-powers-of-beta-26", "shift-powers-of-beta");
impl_web!(ShiftedDegree27, "shifted-powers-of-beta-27", "shift-powers-of-beta");

// Powers of Beta Times Gamma * G
impl_web!(Gamma, "powers-of-beta-gamma", "powers-of-beta-gamma");
// Negative Powers of Beta in G2
impl_web!(NegBeta, "neg-powers-of-beta", "neg-powers-of-beta");
// Negative Powers of Beta in G2
impl_web!(BetaH, "beta-h", "beta-h");

// Credits
impl_web!(TestProver, "test", "prover");
impl_web!(MintProver, "mint", "prover");
impl_web!(MintVerifier, "mint", "verifier");
impl_web!(TransferProver, "transfer", "prover");
impl_web!(TransferVerifier, "transfer", "verifier");
impl_web!(JoinProver, "join", "prover");
impl_web!(JoinVerifier, "join", "verifier");
impl_web!(SplitProver, "split", "prover");
impl_web!(SplitVerifier, "split", "verifier");
impl_web!(FeeProver,"fee", "prover");
impl_web!(FeeVerifier, "fee", "verifier");

// Inclusion
impl_web!(InclusionProver, "inclusion", "prover");
impl_web!(InclusionVerifier, "inclusion", "verifier");

#[macro_export]
macro_rules! insert_credit_keys {
    ($map:ident, $type:ident<$network:ident>, $variant:ident) => {{
        paste::paste! {
            let string = stringify!([<$variant:lower>]);
            $crate::insert_key!($map, string, $type<$network>, ("mint", $crate::testnet3::[<Mint $variant>]::load_bytes()));
            $crate::insert_key!($map, string, $type<$network>, ("transfer", $crate::testnet3::[<Transfer $variant>]::load_bytes()));
            $crate::insert_key!($map, string, $type<$network>, ("join", $crate::testnet3::[<Join $variant>]::load_bytes()));
            $crate::insert_key!($map, string, $type<$network>, ("split", $crate::testnet3::[<Split $variant>]::load_bytes()));
            $crate::insert_key!($map, string, $type<$network>, ("fee", $crate::testnet3::[<Fee $variant>]::load_bytes()));
        }
    }};
}

#[macro_export]
macro_rules! insert_key {
    ($map:ident, $string:tt, $type:ident<$network:ident>, ($name:tt, $circuit_key:expr)) => {{
        // Load the circuit key bytes.
        let key_bytes: Vec<u8> = $circuit_key.expect(&format!("Failed to load {} bytes", $string));
        // Recover the circuit key.
        let key = $type::<$network>::from_bytes_le(&key_bytes[2..]).expect(&format!("Failed to recover {}", $string));
        // Insert the circuit key.
        $map.insert($name.to_string(), std::sync::Arc::new(key));
    }};
}

// // Inclusion
// impl_remote!(InclusionProver, REMOTE_URL, "resources/", "inclusion", "prover");
// impl_remote!(InclusionVerifier, REMOTE_URL, "resources/", "inclusion", "verifier");

/// The function name for the inclusion circuit.
pub const TESTNET3_INCLUSION_FUNCTION_NAME: &str = "inclusion";

lazy_static! {
    pub static ref INCLUSION_PROVING_KEY: Vec<u8> =
        InclusionProver::load_bytes().expect("Failed to load inclusion proving key");
    pub static ref INCLUSION_VERIFYING_KEY: Vec<u8> =
        InclusionVerifier::load_bytes().expect("Failed to load inclusion verifying key");
}
