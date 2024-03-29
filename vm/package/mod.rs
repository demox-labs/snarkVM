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

mod build;
mod clean;
mod deploy;
mod execute;
mod is_build_required;
mod run;

pub use build::{BuildRequest, BuildResponse};
pub use deploy::{DeployRequest, DeployResponse};

use crate::{
    console::{
        account::PrivateKey,
        network::Network,
        program::{Identifier, Locator, ProgramID, Response, Value},
    },
    file::{AVMFile, AleoFile, Manifest, ProverFile, VerifierFile, README},
    ledger::{block::Execution, query::Query, store::helpers::memory::BlockMemory},
    prelude::{Deserialize, Deserializer, Serialize, SerializeStruct, Serializer},
    synthesizer::{
        process::{Assignments, CallMetrics, CallStack, Process, StackExecute},
        program::{CallOperator, Instruction, Program},
        snark::{ProvingKey, VerifyingKey},
    },
};

use anyhow::{bail, ensure, Error, Result};
use core::str::FromStr;
use rand::{CryptoRng, Rng};
use std::path::{Path, PathBuf};

#[cfg(feature = "aleo-cli")]
use colored::Colorize;

pub struct Package<N: Network> {
    /// The program ID.
    program_id: ProgramID<N>,
    /// The directory path.
    directory: PathBuf,
    /// The manifest file.
    manifest_file: Manifest<N>,
    /// The program file.
    program_file: AleoFile<N>,
}

impl<N: Network> Package<N> {
    /// Creates a new package, at the given directory with the given program name.
    pub fn create(directory: &Path, program_id: &ProgramID<N>) -> Result<Self> {
        // Ensure the directory path does not exist.
        ensure!(!directory.exists(), "The program directory already exists: {}", directory.display());
        // Ensure the program name is valid.
        ensure!(!Program::is_reserved_keyword(program_id.name()), "Program name is invalid (reserved): {program_id}");

        // Create the program directory.
        if !directory.exists() {
            std::fs::create_dir_all(directory)?;
        }

        // Create the manifest file.
        let manifest_file = Manifest::create(directory, program_id)?;
        // Create the program file.
        let program_file = AleoFile::create(directory, program_id, true)?;
        // Create the README file.
        let _readme_file = README::create::<N>(directory, program_id)?;

        Ok(Self { program_id: *program_id, directory: directory.to_path_buf(), manifest_file, program_file })
    }

    /// Opens the package at the given directory with the given program name.
    pub fn open(directory: &Path) -> Result<Self> {
        // Ensure the directory path exists.
        ensure!(directory.exists(), "The program directory does not exist: {}", directory.display());
        // Ensure the manifest file exists.
        ensure!(
            Manifest::<N>::exists_at(directory),
            "Missing '{}' at '{}'",
            Manifest::<N>::file_name(),
            directory.display()
        );
        // Ensure the main program file exists.
        ensure!(
            AleoFile::<N>::main_exists_at(directory),
            "Missing '{}' at '{}'",
            AleoFile::<N>::main_file_name(),
            directory.display()
        );

        // Open the manifest file.
        let manifest_file = Manifest::open(directory)?;
        // Retrieve the program ID.
        let program_id = *manifest_file.program_id();
        // Ensure the program name is valid.
        ensure!(!Program::is_reserved_keyword(program_id.name()), "Program name is invalid (reserved): {program_id}");

        // Open the program file.
        let program_file = AleoFile::open(directory, &program_id, true)?;

        Ok(Self { program_id, directory: directory.to_path_buf(), manifest_file, program_file })
    }

    /// Returns the program ID.
    pub const fn program_id(&self) -> &ProgramID<N> {
        &self.program_id
    }

    /// Returns the directory path.
    pub const fn directory(&self) -> &PathBuf {
        &self.directory
    }

    /// Returns the manifest file.
    pub const fn manifest_file(&self) -> &Manifest<N> {
        &self.manifest_file
    }

    /// Returns the program file.
    pub const fn program_file(&self) -> &AleoFile<N> {
        &self.program_file
    }

    /// Returns the program.
    pub const fn program(&self) -> &Program<N> {
        self.program_file.program()
    }

    /// Returns the build directory.
    pub fn build_directory(&self) -> PathBuf {
        self.directory.join("build")
    }

    /// Returns the imports directory.
    pub fn imports_directory(&self) -> PathBuf {
        self.directory.join("imports")
    }

    /// Returns a new process for the package.
    pub fn get_process(&self) -> Result<Process<N>> {
        // Create the process.
        let mut process = Process::load()?;

        // Prepare the imports directory.
        let imports_directory = self.imports_directory();

        // Initialize the 'credits.aleo' program ID.
        let credits_program_id = ProgramID::<N>::from_str("credits.aleo")?;

        // Add all import programs (in order) to the process.
        self.program().imports().keys().try_for_each(|program_id| {
            // Don't add `credits.aleo` as the process is already loaded with it.
            if program_id != &credits_program_id {
                // Open the Aleo program file.
                let import_program_file = AleoFile::open(&imports_directory, program_id, false)?;
                // Add the import program.
                process.add_program(import_program_file.program())?;
            }
            Ok::<_, Error>(())
        })?;

        // Add the program to the process.
        process.add_program(self.program())?;

        Ok(process)
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use snarkvm_console::{account::Address, network::MainnetV0, prelude::TestRng};

    use std::{fs::File, io::Write};

    type CurrentNetwork = MainnetV0;

    fn temp_dir() -> PathBuf {
        tempfile::tempdir().expect("Failed to open temporary directory").into_path()
    }

    /// Samples a (temporary) package containing a `token.aleo` program.
    pub(crate) fn sample_token_package() -> (PathBuf, Package<CurrentNetwork>) {
        // Initialize the program.
        let program = Program::<CurrentNetwork>::from_str(
            r"
            import credits.aleo;
            program arc_0038.aleo;
            
            // Constants
            // ADMIN: address = aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs - the admin address is the address of the contract creator
            // CORE_PROTOCOL: address = aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt - the address of this program
            // SHARES_TO_MICROCREDITS: u64 = 1000u64;
            // PRECISION_UNSIGNED: u128 = 1000u128;
            // MAX_COMMISSION_RATE: u128 = 500u128;
            // UNBONDING_PERIOD: u32 = 360u32;
            // MINIMUM_BOND_AMOUNT: u64 = 1000000000u64;
            
            struct withdrawal_state:
                microcredits as u64;
                claim_block as u32;
            
            // copied from credits.aleo, as structs are not importable
            struct bond_state:
                // The address of the validator.
                validator as address;
                // The amount of microcredits that are currently bonded to the specified validator.
                microcredits as u64;
            
            // copied from credits.aleo, as structs are not importable
            // The `unbond_state` struct tracks the microcredits that are currently unbonding, along with the unlock height.
            struct unbond_state:
                // The amount of microcredits that are currently unbonding.
                microcredits as u64;
                // The block height at which the unbonding will be complete, and can be claimed.
                height as u32;
            
            // 0u8 -> Whether the program has been initialized
            mapping is_initialized:
                key as u8.public;
                value as boolean.public;
            
            
            // Commission rate: 0u8 -> u128
            //  * percentage of rewards taken as commission
            //  * relative to precision of 1000
            //  * e.g. 100u128 = 10%
            mapping commission_percent:
                key as u8.public;
                value as u128.public;
            
            
            // 0u8 -> address of validator
            // 1u8 -> the address of the next validator, automatically updated after calling bond_all
            mapping validator:
                key as u8.public;
                value as address.public;
            
            
            // 0u8 -> total balance of microcredits pooled
            mapping total_balance:
                key as u8.public;
                value as u64.public;
            
            
            // 0u8 -> balance of deposits that have not been bonded, updated when calling bond_all
            mapping pending_deposits:
                key as u8.public;
                value as u64.public;
            
            
            // 0u8 -> total pool of delegator shares
            mapping total_shares:
                key as u8.public;
                value as u64.public;
            
            
            // address -> number of shares held by the delegator with this address
            mapping delegator_shares:
                key as address.public;
                value as u64.public;
            
            
            // 0u8 -> balance pending withdrawal currently unbonding
            // 1u8 -> balance pending withdrawal owned by the program
            mapping pending_withdrawal:
                key as u8.public;
                value as u64.public;
            
            
            // Unbonding allowed: 0u8 ->
            //   * The height at which the current withdrawal batch will be done unbonding
            //   * if not present or == 0u32, a new batch can begin unbonding
            mapping current_batch_height:
                key as u8.public;
                value as u32.public;
            
            
            // address -> pending withdrawal for the delegator with this address
            mapping withdrawals:
                key as address.public;
                value as withdrawal_state.public;
            
            function initialize:
                input r0 as u128.public;
                input r1 as address.public;
                assert.eq self.caller aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs;
                lt r0 1000u128 into r2;
                assert.eq r2 true;
                lte r0 500u128 into r3;
                assert.eq r3 true;
                async initialize r0 r1 into r4;
                output r4 as arc_0038.aleo/initialize.future;
            
            finalize initialize:
                input r0 as u128.public;
                input r1 as address.public;
                get.or_use is_initialized[0u8] false into r2;
                assert.eq r2 false;
                set true into is_initialized[0u8];
                set r0 into commission_percent[0u8];
                set r1 into validator[0u8];
                set 0u64 into total_shares[0u8];
                set 0u64 into total_balance[0u8];
                set 0u64 into pending_deposits[0u8];
                set 0u64 into pending_withdrawal[0u8];
                set 0u64 into pending_withdrawal[1u8];
                set 0u32 into current_batch_height[0u8];
            
            
            function initial_deposit:
                input r0 as u64.public;
                input r1 as address.public;
                assert.eq self.caller aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs;
                call credits.aleo/transfer_public_as_signer aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt r0 into r2;
                call credits.aleo/bond_public r1 aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt r0 into r3;
                async initial_deposit r2 r3 r0 r1 into r4;
                output r4 as arc_0038.aleo/initial_deposit.future;
            
            finalize initial_deposit:
                input r0 as credits.aleo/transfer_public_as_signer.future;
                input r1 as credits.aleo/bond_public.future;
                input r2 as u64.public;
                input r3 as address.public;
                await r0;
                await r1;
                get is_initialized[0u8] into r4;
                assert.eq r4 true;
                get validator[0u8] into r5;
                assert.eq r5 r3;
                get.or_use total_balance[0u8] 0u64 into r6;
                get.or_use total_shares[0u8] 0u64 into r7;
                assert.eq r6 0u64;
                assert.eq r7 0u64;
                set r2 into total_balance[0u8];
                mul r2 1000u64 into r8;
                set r8 into total_shares[0u8];
                set r8 into delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs];
            
            
            
            
            function get_commission_test:
                input r0 as u128.private;
                input r1 as u128.private;
                mul r0 r1 into r2;
                div r2 1000u128 into r3;
                cast r3 into r4 as u64;
                output r4 as u64.private;
            
            
            
            
            function calculate_new_shares_test:
                input r0 as u128.private;
                input r1 as u128.private;
                input r2 as u128.private;
                input r3 as u128.private;
                add r0 r1 into r4;
                mul r3 1000u128 into r5;
                add r4 r2 into r6;
                mul r5 r6 into r7;
                mul r4 1000u128 into r8;
                div r7 r8 into r9;
                sub r9 r3 into r10;
                cast r10 into r11 as u64;
                output r11 as u64.private;
            
            
            function set_commission_percent:
                input r0 as u128.public;
                assert.eq self.caller aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs;
                lt r0 1000u128 into r1;
                assert.eq r1 true;
                lte r0 500u128 into r2;
                assert.eq r2 true;
                async set_commission_percent r0 into r3;
                output r3 as arc_0038.aleo/set_commission_percent.future;
            
            finalize set_commission_percent:
                input r0 as u128.public;
            // Make sure all commission is claimed before changing the rate
                cast aleo1q6qstg8q8shwqf5m6q5fcenuwsdqsvp4hhsgfnx5chzjm3secyzqt9mxm8 0u64 into r1 as bond_state;
                get.or_use credits.aleo/bonded[aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt] r1 into r2;
                get total_balance[0u8] into r3;
                get total_shares[0u8] into r4;
                gt r2.microcredits r3 into r5;
                sub r2.microcredits r3 into r6;
                ternary r5 r6 0u64 into r7;
                get commission_percent[0u8] into r8;
                cast r7 into r9 as u128;
                mul r9 r8 into r10;
                div r10 1000u128 into r11;
                cast r11 into r12 as u64;
                sub r7 r12 into r13;
                add r3 r13 into r14;
                get pending_deposits[0u8] into r15;
                cast r14 into r16 as u128;
                cast r15 into r17 as u128;
                cast r12 into r18 as u128;
                cast r4 into r19 as u128;
                add r16 r17 into r20;
                mul r19 1000u128 into r21;
                add r20 r18 into r22;
                mul r21 r22 into r23;
                mul r20 1000u128 into r24;
                div r23 r24 into r25;
                sub r25 r19 into r26;
                cast r26 into r27 as u64;
                get.or_use delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs] 0u64 into r28;
                add r28 r27 into r29;
                set r29 into delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs];
                add r4 r27 into r30;
                set r30 into total_shares[0u8];
                add r14 r12 into r31;
                set r31 into total_balance[0u8];
            // Set the new commission rate
                set r0 into commission_percent[0u8];
            
            
            // Update the validator address, to be applied automatically on the next bond_all call
            function set_next_validator:
                input r0 as address.public;
                assert.eq self.caller aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs;
                async set_next_validator r0 into r1;
                output r1 as arc_0038.aleo/set_next_validator.future;
            
            finalize set_next_validator:
                input r0 as address.public;
                set r0 into validator[1u8];
            
            
            function unbond_all:
                input r0 as u64.public;
                call credits.aleo/unbond_public r0 into r1;
                async unbond_all r1 into r2;
                output r2 as arc_0038.aleo/unbond_all.future;
            
            finalize unbond_all:
                input r0 as credits.aleo/unbond_public.future;
                await r0;
                contains validator[1u8] into r1;
                assert.eq r1 true;
                cast aleo1q6qstg8q8shwqf5m6q5fcenuwsdqsvp4hhsgfnx5chzjm3secyzqt9mxm8 0u64 into r2 as bond_state;
                get.or_use credits.aleo/bonded[aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt] r2 into r3;
            // Assert that the pool was fully unbonded
                assert.eq r3.microcredits 0u64;
            // Make sure all commission is claimed
                cast 0u64 0u32 into r4 as unbond_state;
                get.or_use credits.aleo/unbonding[aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt] r4 into r5;
                get pending_withdrawal[0u8] into r6;
                sub r5.microcredits r6 into r7;
                get total_balance[0u8] into r8;
                get total_shares[0u8] into r9;
                gt r7 r8 into r10;
                sub r7 r8 into r11;
                ternary r10 r11 0u64 into r12;
                get commission_percent[0u8] into r13;
                cast r12 into r14 as u128;
                mul r14 r13 into r15;
                div r15 1000u128 into r16;
                cast r16 into r17 as u64;
                sub r12 r17 into r18;
                add r8 r18 into r19;
                get pending_deposits[0u8] into r20;
                cast r19 into r21 as u128;
                cast r20 into r22 as u128;
                cast r17 into r23 as u128;
                cast r9 into r24 as u128;
                add r21 r22 into r25;
                mul r24 1000u128 into r26;
                add r25 r23 into r27;
                mul r26 r27 into r28;
                mul r25 1000u128 into r29;
                div r28 r29 into r30;
                sub r30 r24 into r31;
                cast r31 into r32 as u64;
                get.or_use delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs] 0u64 into r33;
                add r33 r32 into r34;
                set r34 into delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs];
                add r9 r32 into r35;
                set r35 into total_shares[0u8];
                add r19 r17 into r36;
                set r36 into total_balance[0u8];
            
            
            function claim_unbond:
                call credits.aleo/claim_unbond_public into r0;
                async claim_unbond r0 into r1;
                output r1 as arc_0038.aleo/claim_unbond.future;
            
            finalize claim_unbond:
                input r0 as credits.aleo/claim_unbond_public.future;
                await r0;
                remove current_batch_height[0u8];
                get pending_withdrawal[0u8] into r1;
                get pending_withdrawal[1u8] into r2;
                add r2 r1 into r3;
                set 0u64 into pending_withdrawal[0u8];
                set r3 into pending_withdrawal[1u8];
            
            
            function bond_all:
                input r0 as address.public;
                input r1 as u64.public;
            // Call will fail if there is any balance still bonded to another validator
                call credits.aleo/bond_public r0 aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt r1 into r2;
                async bond_all r2 r0 into r3;
                output r3 as arc_0038.aleo/bond_all.future;
            
            finalize bond_all:
                input r0 as credits.aleo/bond_public.future;
                input r1 as address.public;
                await r0;
                get.or_use credits.aleo/account[aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt] 0u64 into r2;
                get pending_withdrawal[1u8] into r3;
                gte r2 r3 into r4;
                assert.eq r4 true;
                cast aleo1q6qstg8q8shwqf5m6q5fcenuwsdqsvp4hhsgfnx5chzjm3secyzqt9mxm8 0u64 into r5 as bond_state;
                get.or_use credits.aleo/bonded[aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt] r5 into r6;
                get total_balance[0u8] into r7;
                get pending_deposits[0u8] into r8;
                add r8 r7 into r9;
                sub r9 r6.microcredits into r10;
                set r10 into pending_deposits[0u8];
                set r6.microcredits into total_balance[0u8];
            // Set validator, call will fail if next validator is not set
                get validator[1u8] into r11;
                assert.eq r1 r11;
                set r11 into validator[0u8];
                remove validator[1u8];
            
            
            function bond_deposits:
                input r0 as address.public;
                input r1 as u64.public;
            // Call will fail if there is any balance still bonded to another validator
                call credits.aleo/bond_public r0 aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt r1 into r2;
                async bond_deposits r2 r1 into r3;
                output r3 as arc_0038.aleo/bond_deposits.future;
            
            finalize bond_deposits:
                input r0 as credits.aleo/bond_public.future;
                input r1 as u64.public;
                await r0;
                get.or_use credits.aleo/account[aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt] 0u64 into r2;
                get pending_withdrawal[1u8] into r3;
                gte r2 r3 into r4;
                assert.eq r4 true;
                get total_balance[0u8] into r5;
                get pending_deposits[0u8] into r6;
                sub r6 r1 into r7;
                set r7 into pending_deposits[0u8];
                add r5 r1 into r8;
                set r8 into total_balance[0u8];
                contains validator[1u8] into r9;
                assert.eq r9 false;
            
            
            // Distribute shares for new commission
            function claim_commission:
                assert.eq self.caller aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs;
                async claim_commission into r0;
                output r0 as arc_0038.aleo/claim_commission.future;
            
            finalize claim_commission:
                cast aleo1q6qstg8q8shwqf5m6q5fcenuwsdqsvp4hhsgfnx5chzjm3secyzqt9mxm8 0u64 into r0 as bond_state;
                get.or_use credits.aleo/bonded[aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt] r0 into r1;
                get total_balance[0u8] into r2;
                get total_shares[0u8] into r3;
                gt r1.microcredits r2 into r4;
                sub r1.microcredits r2 into r5;
                ternary r4 r5 0u64 into r6;
                get commission_percent[0u8] into r7;
                cast r6 into r8 as u128;
                mul r8 r7 into r9;
                div r9 1000u128 into r10;
                cast r10 into r11 as u64;
                sub r6 r11 into r12;
                add r2 r12 into r13;
                get pending_deposits[0u8] into r14;
                cast r13 into r15 as u128;
                cast r14 into r16 as u128;
                cast r11 into r17 as u128;
                cast r3 into r18 as u128;
                add r15 r16 into r19;
                mul r18 1000u128 into r20;
                add r19 r17 into r21;
                mul r20 r21 into r22;
                mul r19 1000u128 into r23;
                div r22 r23 into r24;
                sub r24 r18 into r25;
                cast r25 into r26 as u64;
                get.or_use delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs] 0u64 into r27;
                add r27 r26 into r28;
                set r28 into delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs];
                add r3 r26 into r29;
                set r29 into total_shares[0u8];
                add r13 r11 into r30;
                set r30 into total_balance[0u8];
            
            
            function deposit_public:
                input r0 as u64.public;
                call credits.aleo/transfer_public_as_signer aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt r0 into r1;
                async deposit_public r1 self.caller r0 into r2;
                output r2 as arc_0038.aleo/deposit_public.future;
            
            finalize deposit_public:
                input r0 as credits.aleo/transfer_public_as_signer.future;
                input r1 as address.public;
                input r2 as u64.public;
                await r0;
            // Distribute shares for new commission
                cast aleo1q6qstg8q8shwqf5m6q5fcenuwsdqsvp4hhsgfnx5chzjm3secyzqt9mxm8 0u64 into r3 as bond_state;
                get.or_use credits.aleo/bonded[aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt] r3 into r4;
                get total_balance[0u8] into r5;
                get total_shares[0u8] into r6;
                gt r4.microcredits r5 into r7;
                sub r4.microcredits r5 into r8;
                ternary r7 r8 0u64 into r9;
                get commission_percent[0u8] into r10;
                cast r9 into r11 as u128;
                mul r11 r10 into r12;
                div r12 1000u128 into r13;
                cast r13 into r14 as u64;
                sub r9 r14 into r15;
                add r5 r15 into r16;
                get pending_deposits[0u8] into r17;
                cast r16 into r18 as u128;
                cast r17 into r19 as u128;
                cast r14 into r20 as u128;
                cast r6 into r21 as u128;
                add r18 r19 into r22;
                mul r21 1000u128 into r23;
                add r22 r20 into r24;
                mul r23 r24 into r25;
                mul r22 1000u128 into r26;
                div r25 r26 into r27;
                sub r27 r21 into r28;
                cast r28 into r29 as u64;
                get.or_use delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs] 0u64 into r30;
                add r30 r29 into r31;
                set r31 into delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs];
                add r6 r29 into r32;
                add r16 r14 into r33;
            // Update total balance to include rewards
                set r33 into total_balance[0u8];
            // Calculate shares to mint for deposit
                cast r33 into r34 as u128;
                cast r17 into r35 as u128;
                cast r2 into r36 as u128;
                cast r32 into r37 as u128;
                add r34 r35 into r38;
                mul r37 1000u128 into r39;
                add r38 r36 into r40;
                mul r39 r40 into r41;
                mul r38 1000u128 into r42;
                div r41 r42 into r43;
                sub r43 r37 into r44;
                cast r44 into r45 as u64;
            // Make sure the deposit is not too small
                gte r45 1u64 into r46;
                assert.eq r46 true;
            // Update delegator shares
                get.or_use delegator_shares[r1] 0u64 into r47;
                add r47 r45 into r48;
                set r48 into delegator_shares[r1];
            // Update total shares
                add r32 r45 into r49;
                set r49 into total_shares[0u8];
            // Update pending deposits
                get pending_deposits[0u8] into r50;
                add r50 r2 into r51;
                set r51 into pending_deposits[0u8];
            
            
            
            
            function withdraw_public:
                input r0 as u64.public;
                input r1 as u64.public;
                call credits.aleo/unbond_public r1 into r2;
                async withdraw_public r2 r0 r1 self.caller into r3;
                output r3 as arc_0038.aleo/withdraw_public.future;
            
            finalize withdraw_public:
                input r0 as credits.aleo/unbond_public.future;
                input r1 as u64.public;
                input r2 as u64.public;
                input r3 as address.public;
                await r0;
            // Assert that they don't have any pending withdrawals
                contains withdrawals[r3] into r4;
                assert.eq r4 false;
            // Determine if the withdrawal can fit into the current batch
                get.or_use current_batch_height[0u8] 0u32 into r5;
                add block.height 360u32 into r6;
                is.eq r5 0u32 into r7;
                gte r5 r6 into r8;
                or r7 r8 into r9;
                assert.eq r9 true;
            // Assert that they have enough to withdraw
                get delegator_shares[r3] into r10;
                gte r10 r1 into r11;
                assert.eq r11 true;
            // Prevent a full unbond if there are pending deposits to maintain the minimum bond amount
                cast 0u64 0u32 into r12 as unbond_state;
                get.or_use credits.aleo/unbonding[aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt] r12 into r13;
                get pending_withdrawal[0u8] into r14;
                sub r13.microcredits r14 into r15;
                get pending_deposits[0u8] into r16;
                sub r15 r2 into r17;
                add r17 r16 into r18;
                gte r18 1000000000u64 into r19;
                cast aleo1q6qstg8q8shwqf5m6q5fcenuwsdqsvp4hhsgfnx5chzjm3secyzqt9mxm8 0u64 into r20 as bond_state;
                get.or_use credits.aleo/bonded[aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt] r20 into r21;
                gte r21.microcredits 1000000000u64 into r22;
            // Allow the withdrawal if the pool is still bonded, or if there are not enough deposits to maintain the minimum bond amount
                not r19 into r23;
                or r22 r23 into r24;
                assert.eq r24 true;
            // Add back the withdrawal amount to appropriately calculate rewards before the withdrawal
                add r21.microcredits r2 into r25;
            // Distribute shares for new commission
                get total_balance[0u8] into r26;
                get total_shares[0u8] into r27;
                gt r25 r26 into r28;
                sub r25 r26 into r29;
                ternary r28 r29 0u64 into r30;
                get commission_percent[0u8] into r31;
                cast r30 into r32 as u128;
                mul r32 r31 into r33;
                div r33 1000u128 into r34;
                cast r34 into r35 as u64;
                sub r30 r35 into r36;
                add r26 r36 into r37;
                cast r37 into r38 as u128;
                cast r16 into r39 as u128;
                cast r35 into r40 as u128;
                cast r27 into r41 as u128;
                add r38 r39 into r42;
                mul r41 1000u128 into r43;
                add r42 r40 into r44;
                mul r43 r44 into r45;
                mul r42 1000u128 into r46;
                div r45 r46 into r47;
                sub r47 r41 into r48;
                cast r48 into r49 as u64;
                get.or_use delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs] 0u64 into r50;
                add r50 r49 into r51;
                set r51 into delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs];
                add r27 r49 into r52;
                add r37 r35 into r53;
                cast r53 into r54 as u128;
                cast r16 into r55 as u128;
            // Calculate full pool size
                add r54 r55 into r56;
            // Calculate withdrawal amount
                cast r1 into r57 as u128;
                cast r56 into r58 as u128;
                mul r57 r58 into r59;
                mul r59 1000u128 into r60;
                cast r52 into r61 as u128;
                mul r61 1000u128 into r62;
                div r60 r62 into r63;
                cast r2 into r64 as u128;
            // If the calculated withdrawal amount is greater than total_withdrawal, the excess will stay in the pool
                gte r63 r64 into r65;
                assert.eq r65 true;
            // Update withdrawals mappings
                div block.height 1000u32 into r66;
                mul r66 1000u32 into r67;
                add r67 1000u32 into r68;
                ternary r7 r68 r5 into r69;
                set r69 into current_batch_height[0u8];
                cast r2 r69 into r70 as withdrawal_state;
                set r70 into withdrawals[r3];
            // Update pending withdrawal
                add r14 r2 into r71;
                set r71 into pending_withdrawal[0u8];
            // Update total balance
                sub r53 r2 into r72;
                set r72 into total_balance[0u8];
            // Update total shares
                sub r52 r1 into r73;
                set r73 into total_shares[0u8];
            // Update delegator_shares mapping
                sub r10 r1 into r74;
                set r74 into delegator_shares[r3];
            
            
            function get_new_batch_height_test:
                input r0 as u32.private;
                div r0 1000u32 into r1;
                mul r1 1000u32 into r2;
                add r2 1000u32 into r3;
                output r3 as u32.private;
            
            
            function create_withdraw_claim:
                input r0 as u64.public;
                async create_withdraw_claim r0 self.caller into r1;
                output r1 as arc_0038.aleo/create_withdraw_claim.future;
            
            finalize create_withdraw_claim:
                input r0 as u64.public;
                input r1 as address.public;
            // Assert that they don't have any pending withdrawals
                contains withdrawals[r1] into r2;
                assert.eq r2 false;
            // Assert that the pool is not bonded
                cast aleo1q6qstg8q8shwqf5m6q5fcenuwsdqsvp4hhsgfnx5chzjm3secyzqt9mxm8 0u64 into r3 as bond_state;
                get.or_use credits.aleo/bonded[aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt] r3 into r4;
                assert.eq r4.microcredits 0u64;
            // Assert that the unbonded balance has been claimed
                cast 0u64 0u32 into r5 as unbond_state;
                get.or_use credits.aleo/unbonding[aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt] r5 into r6;
                assert.eq r6.microcredits 0u64;
            // Assert that they have enough to withdraw
                get delegator_shares[r1] into r7;
                gte r7 r0 into r8;
                assert.eq r8 true;
            // Calculate withdrawal amount
                get total_balance[0u8] into r9;
                get pending_deposits[0u8] into r10;
                cast r9 into r11 as u128;
                cast r10 into r12 as u128;
                add r11 r12 into r13;
                get total_shares[0u8] into r14;
                cast r0 into r15 as u128;
                mul r15 r13 into r16;
                mul r16 1000u128 into r17;
                cast r14 into r18 as u128;
                mul r18 1000u128 into r19;
                div r17 r19 into r20;
                cast r20 into r21 as u64;
            // Update withdrawals mappings
                add block.height 1u32 into r22;
                cast r21 r22 into r23 as withdrawal_state;
                set r23 into withdrawals[r1];
            // Update pending withdrawal
                get pending_withdrawal[1u8] into r24;
                add r24 r21 into r25;
                set r25 into pending_withdrawal[1u8];
            // Update total balance
                sub r9 r21 into r26;
                set r26 into total_balance[0u8];
            // Update total shares
                sub r14 r0 into r27;
                set r27 into total_shares[0u8];
            // Update delegator_shares mapping
                sub r7 r0 into r28;
                set r28 into delegator_shares[r1];
            
            
            function claim_withdrawal_public:
                input r0 as address.public;
                input r1 as u64.public;
                call credits.aleo/transfer_public r0 r1 into r2;
                async claim_withdrawal_public r2 r0 r1 into r3;
                output r3 as arc_0038.aleo/claim_withdrawal_public.future;
            
            finalize claim_withdrawal_public:
                input r0 as credits.aleo/transfer_public.future;
                input r1 as address.public;
                input r2 as u64.public;
                await r0;
                get withdrawals[r1] into r3;
            // Assert that the withdrawal amount matches the mapping, and the withdrawal is ready to be claimed
                gte block.height r3.claim_block into r4;
                assert.eq r4 true;
                assert.eq r3.microcredits r2;
            // Remove withdrawal
                remove withdrawals[r1];
            // Update pending withdrawal
                get pending_withdrawal[1u8] into r5;
                sub r5 r2 into r6;
                set r6 into pending_withdrawal[1u8];
            ",
        )
        .unwrap();

        // Sample the package using the program.
        sample_package_with_program_and_imports(&program, &[])
    }

    /// Samples a (temporary) package containing a `wallet.aleo` program which imports `token.aleo`.
    pub(crate) fn sample_wallet_package() -> (PathBuf, Package<CurrentNetwork>) {
        // Initialize the imported program.
        let imported_program = Program::<CurrentNetwork>::from_str(
            "
program token.aleo;

record token:
    owner as address.private;
    amount as u64.private;

function initialize:
    input r0 as address.private;
    input r1 as u64.private;
    cast r0 r1 into r2 as token.record;
    output r2 as token.record;

function transfer:
    input r0 as token.record;
    input r1 as address.private;
    input r2 as u64.private;
    sub r0.amount r2 into r3;
    cast r1 r2 into r4 as token.record;
    cast r0.owner r3 into r5 as token.record;
    output r4 as token.record;
    output r5 as token.record;",
        )
        .unwrap();

        // Initialize the main program.
        let main_program = Program::<CurrentNetwork>::from_str(
            "
import token.aleo;

program wallet.aleo;

function transfer:
    input r0 as token.aleo/token.record;
    input r1 as address.private;
    input r2 as u64.private;
    call token.aleo/transfer r0 r1 r2 into r3 r4;
    output r3 as token.aleo/token.record;
    output r4 as token.aleo/token.record;",
        )
        .unwrap();

        // Sample the package using the main program and imported program.
        sample_package_with_program_and_imports(&main_program, &[imported_program])
    }

    /// Samples a (temporary) package containing a `grandparent.aleo` program which imports `parent.aleo` which imports `child.aleo`.
    pub(crate) fn sample_nested_package() -> (PathBuf, Package<CurrentNetwork>) {
        // Initialize the child program.
        let child_program = Program::<CurrentNetwork>::from_str(
            "
program child.aleo;

record A:
    owner as address.private;
    val as u32.private;

function mint:
    input r0 as address.private;
    input r1 as u32.private;
    cast r0 r1 into r2 as A.record;
    output r2 as A.record;",
        )
        .unwrap();

        // Initialize the parent program.
        let parent_program = Program::<CurrentNetwork>::from_str(
            "
import child.aleo;

program parent.aleo;

function wrapper_mint:
    input r0 as address.private;
    input r1 as u32.private;
    call child.aleo/mint r0 r1 into r2;
    output r2 as child.aleo/A.record;",
        )
        .unwrap();

        // Initialize the grandparent program.
        let grandparent_program = Program::<CurrentNetwork>::from_str(
            "
import child.aleo;
import parent.aleo;

program grandparent.aleo;

function double_wrapper_mint:
    input r0 as address.private;
    input r1 as u32.private;
    call parent.aleo/wrapper_mint r0 r1 into r2;
    output r2 as child.aleo/A.record;",
        )
        .unwrap();

        // Sample the package using the main program and imported program.
        sample_package_with_program_and_imports(&grandparent_program, &[child_program, parent_program])
    }

    /// Samples a (temporary) package containing a `transfer.aleo` program which imports `credits.aleo`.
    pub(crate) fn sample_transfer_package() -> (PathBuf, Package<CurrentNetwork>) {
        // Initialize the imported program.
        let imported_program = Program::credits().unwrap();

        // Initialize the main program.
        let main_program = Program::<CurrentNetwork>::from_str(
            "
import credits.aleo;

program transfer.aleo;

function main:
    input r0 as credits.aleo/credits.record;
    input r1 as address.private;
    input r2 as u64.private;
    call credits.aleo/transfer_private r0 r1 r2 into r3 r4;
    output r3 as credits.aleo/credits.record;
    output r4 as credits.aleo/credits.record;",
        )
        .unwrap();

        // Sample the package using the main program and imported program.
        sample_package_with_program_and_imports(&main_program, &[imported_program])
    }

    /// Samples a (temporary) package using a main program and imported programs.
    pub(crate) fn sample_package_with_program_and_imports(
        main_program: &Program<CurrentNetwork>,
        imported_programs: &[Program<CurrentNetwork>],
    ) -> (PathBuf, Package<CurrentNetwork>) {
        // Initialize a temporary directory.
        let directory = temp_dir();

        // If there are imports, create the imports directory.
        if !imported_programs.is_empty() {
            let imports_directory = directory.join("imports");
            std::fs::create_dir_all(&imports_directory).unwrap();

            // Add the imported programs.
            for imported_program in imported_programs {
                let imported_program_id = imported_program.id();

                // Write the imported program string to an imports file in the temporary directory.
                let import_filepath = imports_directory.join(imported_program_id.to_string());
                let mut file = File::create(import_filepath).unwrap();
                file.write_all(imported_program.to_string().as_bytes()).unwrap();
            }
        }

        // Initialize the main program ID.
        let main_program_id = main_program.id();

        // Write the program string to a file in the temporary directory.
        let main_filepath = directory.join("main.aleo");
        let mut file = File::create(main_filepath).unwrap();
        file.write_all(main_program.to_string().as_bytes()).unwrap();

        // Create the manifest file.
        let _manifest_file = Manifest::create(&directory, main_program_id).unwrap();

        // Open the package at the temporary directory.
        let package = Package::<MainnetV0>::open(&directory).unwrap();
        assert_eq!(package.program_id(), main_program_id);

        // Return the temporary directory and the package.
        (directory, package)
    }

    /// Samples a candidate input to execute the sample package.
    pub(crate) fn sample_package_run(
        program_id: &ProgramID<CurrentNetwork>,
    ) -> (PrivateKey<CurrentNetwork>, Identifier<CurrentNetwork>, Vec<Value<CurrentNetwork>>) {
        // Initialize an RNG.
        let rng = &mut TestRng::default();

        match program_id.to_string().as_str() {
            "token.aleo" => {
                // Sample a random private key.
                let private_key = crate::cli::helpers::dotenv_private_key().unwrap();
                let caller = Address::try_from(&private_key).unwrap();

                // Initialize the function name.
                let function_name = Identifier::from_str("initialize").unwrap();

                // Initialize the function inputs.
                let r0 = Value::from_str(&caller.to_string()).unwrap();
                let r1 = Value::from_str("100u64").unwrap();

                (private_key, function_name, vec![r0, r1])
            }
            "wallet.aleo" => {
                // Initialize caller 0.
                let caller0_private_key = crate::cli::helpers::dotenv_private_key().unwrap();
                let caller0 = Address::try_from(&caller0_private_key).unwrap();

                // Initialize caller 1.
                let caller1_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
                let caller1 = Address::try_from(&caller1_private_key).unwrap();

                // Declare the function name.
                let function_name = Identifier::from_str("transfer").unwrap();

                // Initialize the function inputs.
                let r0 = Value::<CurrentNetwork>::from_str(&format!(
                    "{{ owner: {caller0}.private, amount: 100u64.private, _nonce: 0group.public }}"
                ))
                .unwrap();
                let r1 = Value::<CurrentNetwork>::from_str(&caller1.to_string()).unwrap();
                let r2 = Value::<CurrentNetwork>::from_str("99u64").unwrap();

                (caller0_private_key, function_name, vec![r0, r1, r2])
            }
            "grandparent.aleo" => {
                // Initialize caller 0.
                let caller0_private_key = crate::cli::helpers::dotenv_private_key().unwrap();

                // Initialize caller 1.
                let caller1_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
                let caller1 = Address::try_from(&caller1_private_key).unwrap();

                // Declare the function name.
                let function_name = Identifier::from_str("double_wrapper_mint").unwrap();

                // Initialize the function inputs.
                let r0 = Value::<CurrentNetwork>::from_str(&caller1.to_string()).unwrap();
                let r1 = Value::<CurrentNetwork>::from_str("1u32").unwrap();

                (caller0_private_key, function_name, vec![r0, r1])
            }
            _ => panic!("Invalid program ID for sample package (while testing)"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prelude::MainnetV0;
    use snarkvm_utilities::TestRng;

    type CurrentAleo = snarkvm_circuit::network::AleoV0;
    type CurrentNetwork = MainnetV0;

    #[test]
    fn test_imports_directory() {
        // Samples a new package at a temporary directory.
        let (directory, package) = crate::package::test_helpers::sample_token_package();

        // Ensure the imports directory is correct.
        assert_eq!(package.imports_directory(), directory.join("imports"));
        // Ensure the imports directory does *not* exist, when the package does not contain imports.
        assert!(!package.imports_directory().exists());

        // Proactively remove the temporary directory (to conserve space).
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn test_imports_directory_with_an_import() {
        // Samples a new package with an import at a temporary directory.
        let (directory, package) = crate::package::test_helpers::sample_wallet_package();

        // Ensure the imports directory is correct.
        assert_eq!(package.imports_directory(), directory.join("imports"));
        // Ensure the imports directory exists, as the package contains an import.
        assert!(package.imports_directory().exists());

        // Proactively remove the temporary directory (to conserve space).
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn test_build_directory() {
        // Samples a new package at a temporary directory.
        let (directory, package) = crate::package::test_helpers::sample_token_package();

        // Ensure the build directory is correct.
        assert_eq!(package.build_directory(), directory.join("build"));
        // Ensure the build directory does *not* exist, when the package has not been built.
        assert!(!package.build_directory().exists());

        // Proactively remove the temporary directory (to conserve space).
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn test_get_process() {
        // Samples a new package at a temporary directory.
        let (directory, package) = crate::package::test_helpers::sample_token_package();

        // Get the program process and check all instructions.
        assert!(package.get_process().is_ok());

        // Proactively remove the temporary directory (to conserve space).
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn test_package_run_and_execute_match() {
        // Initialize the program.
        let program = Program::<CurrentNetwork>::from_str(
            "
program foo.aleo;

function bar:
    input r0 as boolean.private;
    assert.eq r0 false;",
        )
        .unwrap();

        // Samples a new package at a temporary directory.
        let (directory, package) = crate::package::test_helpers::sample_package_with_program_and_imports(&program, &[]);

        // Ensure the build directory does *not* exist.
        assert!(!package.build_directory().exists());
        // Build the package.
        package.build::<CurrentAleo>(None).unwrap();
        // Ensure the build directory exists.
        assert!(package.build_directory().exists());

        // Initialize an RNG.
        let rng = &mut TestRng::default();
        // Sample the function inputs.
        let private_key = PrivateKey::new(rng).unwrap();
        let function_name = Identifier::from_str("bar").unwrap();
        let inputs = vec![Value::from_str("true").unwrap()];

        // Construct the endpoint.
        let endpoint = "https://api.explorer.aleo.org/v1".to_string();

        // Run the program function.
        let run_result = package.run::<CurrentAleo, _>(&private_key, function_name, &inputs, rng).ok();

        // Execute the program function.
        let execute_result =
            package.execute::<CurrentAleo, _>(endpoint, &private_key, function_name, &inputs, rng).ok();

        match (run_result, execute_result) {
            // If both results are `None`, then they both failed.
            (None, None) => {}
            // If both results are `Some`, then check that the responses match.
            (Some((run_response, _)), Some((execute_response, _, _))) => {
                assert_eq!(run_response, execute_response);
            }
            // Otherwise, the results do not match.
            _ => panic!("Run and execute results do not match"),
        }

        // Proactively remove the temporary directory (to conserve space).
        std::fs::remove_dir_all(directory).unwrap();
    }
}
