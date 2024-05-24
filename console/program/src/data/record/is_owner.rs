// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<N: Network> Record<N, Ciphertext<N>> {
    /// Decrypts `self` into plaintext using the given view key.
    pub fn is_owner(&self, view_key: &ViewKey<N>) -> bool {
        // Compute the address.
        let address = view_key.to_address();
        // Check if the address is the owner.
        self.is_owner_with_address_x_coordinate(view_key, &address.to_x_coordinate())
    }

    pub fn is_owner_direct(
        address_x_coordinate: Field<N>,
        view_key_scalar: Scalar<N>,
        record_nonce: Group<N>,
        record_owner_x_coordinate: Field<N>
    ) -> bool {
        let record_view_key = (record_nonce * view_key_scalar).to_x_coordinate();
        // Compute the 0th randomizer.
        let randomizer = N::hash_many_psd8(&[N::encryption_domain(), record_view_key], 1);
        // Decrypt the owner.
        let owner_x = record_owner_x_coordinate - &randomizer[0];
        // Check if the address is the owner.
        owner_x == address_x_coordinate
    }

    /// Decrypts `self` into plaintext using the x-coordinate of the address corresponding to the given view key.
    pub fn is_owner_with_address_x_coordinate(&self, view_key: &ViewKey<N>, address_x_coordinate: &Field<N>) -> bool {
        // In debug mode, check that the address corresponds to the given view key.
        debug_assert_eq!(
            &view_key.to_address().to_x_coordinate(),
            address_x_coordinate,
            "Failed to check record - view key and address do not match"
        );

        match &self.owner {
            // If the owner is public, check if the address is the owner.
            Owner::Public(owner) => &owner.to_x_coordinate() == address_x_coordinate,
            // If the owner is private, decrypt the owner to check if it matches the address.
            Owner::Private(ciphertext) => {
                // Compute the record view key.
                let record_view_key = (self.nonce * **view_key).to_x_coordinate();
                // Compute the 0th randomizer.
                let randomizer = N::hash_many_psd8(&[N::encryption_domain(), record_view_key], 1);
                // Decrypt the owner.
                let owner_x = ciphertext[0] - randomizer[0];
                // Compare the x coordinates of computed and supplied addresses.
                // We can skip recomputing the address from `owner_x` due to the following reasoning.
                // First, the transaction SNARK that generated the ciphertext would have checked that the ciphertext encrypts a valid address.
                // Now, since a valid address is an element of the prime-order subgroup of the curve, we know that the encrypted x-coordinate corresponds to a prime-order element.
                // Finally, since the SNARK + hybrid encryption
                // together are an authenticated encryption scheme, we know that the ciphertext has not been malleated.
                // Thus overall we know that if the x-coordinate matches that of `address`, then the underlying `address`es must also match.
                // Therefore we can skip recomputing the address from `owner_x` and instead compare the x-coordinates directly.
                &owner_x == address_x_coordinate
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::fs::{self, File};

    use super::*;
    use crate::Literal;
    use snarkvm_console_account::PrivateKey;
    use snarkvm_console_network::MainnetV0;
    use snarkvm_console_types::Field;

    type CurrentNetwork = MainnetV0;

    const ITERATIONS: u64 = 1_000;

    fn check_is_owner<N: Network>(
        file: &mut fs::File,
        view_key: ViewKey<N>,
        owner: Owner<N, Plaintext<N>>,
        rng: &mut TestRng,
    ) -> Result<()> {
        // Prepare the record.
        let randomizer = Scalar::rand(rng);
        let nonce_to_use = N::g_scalar_multiply(&randomizer);
        // println!("nonce_to_use: {:?}", nonce_to_use);
        // println!("nonce x: {:?}", nonce_to_use.to_x_coordinate());
        // println!("nonce y: {:?}", nonce_to_use.to_y_coordinate());
        // println!("view key scalar: {:?}", **view_key);
        // println!("owner address x: {:?}", view_key.to_address().to_x_coordinate());
        // println!("owner address y: {:?}", view_key.to_address().to_y_coordinate());
        let record = Record {
            owner,
            data: IndexMap::from_iter(vec![
                (Identifier::from_str("a")?, Entry::Private(Plaintext::from(Literal::Field(Field::rand(rng))))),
                (Identifier::from_str("b")?, Entry::Private(Plaintext::from(Literal::Scalar(Scalar::rand(rng))))),
            ]),
            nonce: nonce_to_use,
        };

        // Encrypt the record.
        let ciphertext = record.encrypt(randomizer)?;

        match &ciphertext.owner {
            Owner::Public(owner) => {
                println!("unencrypted owner x: {:?}", owner.to_x_coordinate());
                println!("unencrypted owner y: {:?}", owner.to_y_coordinate());
            }
            Owner::Private(ciphertext) => {
                // println!("encrypted owner x: {:?}", ciphertext[0]);
                // print multiple lines in the format of:
                // {
                //   "transition_id": "au19kxv922l2s5cx9e58r08p0f6w5vt5tcde9wwra937ux8ppuk6yzq2pcgg4",
                //   "nonce_x": "251177372049600189482197429390397796266018568297541178545240074020288598514",
                //   "nonce_y": "6249265362832442135861461570942059724436225086028474204208688225599637084489",
                //   "owner_x": "296095557076246474285179298247870355682512885115572813674288110571104591733",
                //   "output_index": 0
                // },
                println!("{{");
                // set semi random transition id, just for keeping track of the tested ciphertext
                println!("\"transition_id\": \"{}\",", strip_letter_chars(nonce_to_use.to_x_coordinate().to_string()));
                println!("\"nonce_x\": \"{}\",", strip_letter_chars(nonce_to_use.to_x_coordinate().to_string()));
                println!("\"nonce_y\": \"{}\",", strip_letter_chars(nonce_to_use.to_y_coordinate().to_string()));
                println!("\"owner_x\": \"{}\",", strip_letter_chars(ciphertext[0].to_string()));
                println!("\"output_index\": 0");
                println!("}},");
                let output_string = format!("{{\n\"transition_id\": \"{}\",\n\"nonce_x\": \"{}\",\n\"nonce_y\": \"{}\",\n\"owner_x\": \"{}\",\n\"output_index\": 0\n}},\n", strip_letter_chars(nonce_to_use.to_x_coordinate().to_string()), strip_letter_chars(nonce_to_use.to_x_coordinate().to_string()), strip_letter_chars(nonce_to_use.to_y_coordinate().to_string()), strip_letter_chars(ciphertext[0].to_string()));
                file.write_all(output_string.as_bytes())?;
            }
        }

        // Ensure the record belongs to the owner.
        assert!(ciphertext.is_owner(&view_key));

        // Sample a random view key and address.
        let private_key = PrivateKey::<N>::new(rng)?;
        let view_key = ViewKey::try_from(&private_key)?;

        // Ensure the random address is not the owner.
        assert!(!ciphertext.is_owner(&view_key));

        Ok(())
    }

    fn strip_letter_chars(s: String) -> String {
        s.chars().filter(|c| c.is_numeric()).collect()
    }

    #[test]
    fn test_is_owner() -> Result<()> {
        let mut rng = TestRng::default();

        // Sample a view key and address.
        let private_key = PrivateKey::<CurrentNetwork>::new(&mut rng)?;
        let view_key = ViewKey::try_from(&private_key)?;
        let address = Address::try_from(&private_key)?;

        println!("view key scalar: {:?}", **view_key);
        println!("address x: {:?}", address.to_x_coordinate());

        // create file to store output to
        let mut file = File::create("output.txt")?;

        // append view key scalar and address x to file
        file.write_all(format!("view key scalar: {:?}\n", **view_key).as_bytes())?;
        file.write_all(format!("address x: {:?}\n", address.to_x_coordinate()).as_bytes())?;

        for _ in 0..1_000 {
            // Public owner.
            // let owner = Owner::Public(address);
            // check_is_owner::<CurrentNetwork>(view_key, owner, &mut rng)?;

            // Private owner.
            let owner = Owner::Private(Plaintext::from(Literal::Address(address)));
            check_is_owner::<CurrentNetwork>(&mut file, view_key, owner, &mut rng)?;
        }
        Ok(())
    }
}
