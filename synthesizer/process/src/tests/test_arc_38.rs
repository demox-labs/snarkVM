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

use crate::Process;
use circuit::network::AleoV0;
use console::{
    account::{Address, PrivateKey},
    network::{prelude::*, MainnetV0},
    program::{Identifier, Literal, Plaintext, ProgramID, Value},
    types::{U64, U8},
};
use ledger_committee::{MIN_DELEGATOR_STAKE, MIN_VALIDATOR_STAKE};
use ledger_query::Query;
use ledger_store::{
    atomic_finalize,
    helpers::memory::{BlockMemory, FinalizeMemory},
    BlockStore,
    FinalizeMode,
    FinalizeStorage,
    FinalizeStore,
};
use synthesizer_program::{FinalizeGlobalState, FinalizeStoreTrait, Program};

use indexmap::IndexMap;

use super::arc_38::arc_38_program;

type CurrentNetwork = MainnetV0;
type CurrentAleo = AleoV0;

const NUM_BLOCKS_TO_UNLOCK: u32 = 360;
fn ADMIN_PK() -> PrivateKey<CurrentNetwork> {
    PrivateKey::from_str("APrivateKey1zkpAzQRSfdgT7oa54XjcsabzptLKMH8XyCSS7H2gjJfRDxj").unwrap()
}

fn ADMIN_PUB_KEY() -> Address<CurrentNetwork> {
    Address::from_str("aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs").unwrap()
}

fn PROTOCOL_ADDRESS() -> Address<CurrentNetwork> {
    Address::from_str("aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt").unwrap()
    // Address::from_str("arc_0038.aleo").unwrap()
}

fn SAMPLE_ADDRESS() -> Address<CurrentNetwork> {
    // Private Key  APrivateKey1zkp67B9CAP5PY4UYEY1NkTGG1JEyxU1bk2H4qUnnLzRaP2r
    //  View Key  AViewKey1ixDM9YbrN1wp17BDLSxcBorYuB6mhNw77TfgHcCoam69
    //   Address  aleo1zmdjtqhn23068h7tl7m7mqhhvm77gdamws79h36z46m74kvggqgsves5wn
    Address::from_str("aleo1zmdjtqhn23068h7tl7m7mqhhvm77gdamws79h36z46m74kvggqgsves5wn").unwrap()
}

/// Samples a new finalize store.
macro_rules! sample_finalize_store {
    () => {{
        #[cfg(feature = "rocks")]
        let temp_dir = tempfile::tempdir().expect("Failed to open temporary directory");
        #[cfg(not(feature = "rocks"))]
        let temp_dir = ();

        #[cfg(feature = "rocks")]
        let store = FinalizeStore::<CurrentNetwork, ledger_store::helpers::rocksdb::FinalizeDB<_>>::open_testing(
            temp_dir.path().to_owned(),
            None,
        )
        .unwrap();
        #[cfg(not(feature = "rocks"))]
        let store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

        (store, temp_dir)
    }};
}

macro_rules! test_atomic_finalize {
    ($store:ident, $mode:expr, $test:block) => {{
        // The test closure.
        let mut run = || -> Result<()> { atomic_finalize!($store, $mode, $test) };
        // Run the test.
        run()
    }};
}

/// Samples a new finalize state.
fn sample_finalize_state(block_height: u32) -> FinalizeGlobalState {
    FinalizeGlobalState::from(block_height as u64, block_height, [0u8; 32])
}

/// Returns the `value` for the given `key` in the `mapping` for the given `program_id`.
fn get_mapping_value<N: Network, F: FinalizeStorage<N>>(
    store: &FinalizeStore<N, F>,
    program_id: &str,
    mapping: &str,
    key: Literal<N>,
) -> Result<Option<Value<N>>> {
    // Prepare the program ID, mapping name, and key.
    let program_id = ProgramID::from_str(program_id)?;
    let mapping = Identifier::from_str(mapping)?;
    let key = Plaintext::from(key);
    // Retrieve the value from the finalize store.
    match store.get_value_speculative(program_id, mapping, &key) {
        Ok(result) => Ok(result),
        Err(err) => bail!("Error getting value for program_id: {program_id}, mapping: {mapping}, key: {key}: {err}"),
    }
}

/// Get the current `account` mapping balance.
fn account_balance<N: Network, F: FinalizeStorage<N>>(
    store: &FinalizeStore<N, F>,
    address: &Address<N>,
) -> Result<u64> {
    // Retrieve the balance from the finalize store.
    match get_mapping_value(store, "credits.aleo", "account", Literal::Address(*address))? {
        Some(Value::Plaintext(Plaintext::Literal(Literal::U64(balance), _))) => Ok(*balance),
        _ => bail!("Missing or malformed account balance for {address}"),
    }
}

/// Get the current committee state from the `committee` mapping for the given validator address.
/// Returns the `committee_state` as a tuple of `(microcredits, is_open)`.
fn committee_state<N: Network, F: FinalizeStorage<N>>(
    store: &FinalizeStore<N, F>,
    address: &Address<N>,
) -> Result<Option<(u64, bool)>> {
    // Retrieve the committee state from the finalize store.
    let state = match get_mapping_value(store, "credits.aleo", "committee", Literal::Address(*address))? {
        Some(Value::Plaintext(Plaintext::Struct(state, _))) => state,
        None => return Ok(None),
        _ => bail!("Malformed committee state for {address}"),
    };

    // Retrieve `microcredits` from the committee state.
    let microcredits = match state.get(&Identifier::from_str("microcredits")?) {
        Some(Plaintext::Literal(Literal::U64(microcredits), _)) => **microcredits,
        _ => bail!("`microcredits` not found for: {address}"),
    };

    // Retrieve `is_open` from the committee state.
    let is_open = match state.get(&Identifier::from_str("is_open")?) {
        Some(Plaintext::Literal(Literal::Boolean(is_open), _)) => **is_open,
        _ => bail!("`is_open` not found for: {address}"),
    };

    Ok(Some((microcredits, is_open)))
}

fn unbond_state<N: Network, F: FinalizeStorage<N>>(
    store: &FinalizeStore<N, F>,
    address: &Address<N>,
) -> Result<Option<(u64, u32)>> {
    // Retrieve the unbonding state from the finalize store.
    let state = match get_mapping_value(store, "credits.aleo", "unbonding", Literal::Address(*address))? {
        Some(Value::Plaintext(Plaintext::Struct(state, _))) => state,
        _ => bail!("Malformed unbonding state for {address}"),
    };

    // Retrieve `microcredits` from the committee state.
    let microcredits = match state.get(&Identifier::from_str("microcredits")?) {
        Some(Plaintext::Literal(Literal::U64(microcredits), _)) => **microcredits,
        _ => bail!("`microcredits` not found for: {address}"),
    };

    // Retrieve `is_open` from the committee state.
    let height = match state.get(&Identifier::from_str("height")?) {
        Some(Plaintext::Literal(Literal::U32(height), _)) => **height,
        _ => bail!("`height` not found for: {address}"),
    };

    Ok(Some((microcredits, height)))
}

fn withdraw_state<N: Network, F: FinalizeStorage<N>>(
    store: &FinalizeStore<N, F>,
    address: &Address<N>,
) -> Result<Option<(u64, u32)>> {
    // Retrieve the unbonding state from the finalize store.
    let state = match get_mapping_value(store, "arc_0038.aleo", "withdrawals", Literal::Address(*address))? {
        Some(Value::Plaintext(Plaintext::Struct(state, _))) => state,
        _ => bail!("Malformed unbonding state for {address}"),
    };

    // Retrieve `microcredits` from the committee state.
    let microcredits = match state.get(&Identifier::from_str("microcredits")?) {
        Some(Plaintext::Literal(Literal::U64(microcredits), _)) => **microcredits,
        _ => bail!("`microcredits` not found for: {address}"),
    };

    // Retrieve `is_open` from the committee state.
    let claim_block = match state.get(&Identifier::from_str("claim_block")?) {
        Some(Plaintext::Literal(Literal::U32(claim_block), _)) => **claim_block,
        _ => bail!("`claim_block` not found for: {address}"),
    };

    Ok(Some((microcredits, claim_block)))
}

fn add_rewards_to_bonded_state<N: Network, F: FinalizeStorage<N>>(
    store: &FinalizeStore<N, F>,
    address: &Address<N>,
    rewards_amount: u64,
) -> Result<()> {
    let program_id = ProgramID::from_str("credits.aleo").unwrap();
    let bonded_mapping = Identifier::from_str("bonded").unwrap();
    let key_address = Plaintext::from(Literal::Address(*address));
    let address_bond = match get_mapping_value(store, "credits.aleo", "bonded", Literal::Address(*address))? {
        Some(Value::Plaintext(Plaintext::Struct(state, _))) => state,
        None => bail!("Missing bonded state for {address}"),
        _ => bail!("Malformed bonded state for {address}"),
    };

    // Retrieve `microcredits` from the committee state.
    let microcredits = match address_bond.get(&Identifier::from_str("microcredits")?) {
        Some(Plaintext::Literal(Literal::U64(microcredits), _)) => **microcredits,
        _ => bail!("`microcredits` not found for: {address}"),
    };

    let validator_address = match address_bond.get(&Identifier::from_str("validator")?) {
        Some(Plaintext::Literal(Literal::Address(address), _)) => *address,
        _ => bail!("`validator` not found for: {address}"),
    };
    println!("Adding rewards to committee state for {:?}", address_bond);
    let updated_microcredits = microcredits + rewards_amount;
    let new_bond_value = Value::from_str(&format!(
        "{{ validator: {validator_address}, microcredits: {updated_microcredits}_u64 }}",
    ))
    .unwrap();

    let _ = store.remove_key_value(program_id, bonded_mapping, &key_address);
    let _ = store.insert_key_value(program_id, bonded_mapping, key_address.clone(), new_bond_value);
    Ok(())
}

/// Get the current bond state from the `bonding` mapping for the given staker address.
/// Returns the `bond_state` as a tuple of `(validator address, microcredits)`.
fn bond_state<N: Network, F: FinalizeStorage<N>>(
    store: &FinalizeStore<N, F>,
    address: &Address<N>,
) -> Result<Option<(Address<N>, u64)>> {
    // Retrieve the bond state from the finalize store.
    let state = match get_mapping_value(store, "credits.aleo", "bonded", Literal::Address(*address))? {
        Some(Value::Plaintext(Plaintext::Struct(state, _))) => state,
        None => return Ok(None),
        _ => bail!("Malformed bond state for {address}"),
    };

    // Retrieve `validator` from the bond state.
    let validator = match state.get(&Identifier::from_str("validator")?) {
        Some(Plaintext::Literal(Literal::Address(address), _)) => *address,
        _ => bail!("`validator` not found for: {address}"),
    };

    // Retrieve `microcredits` from the bond state.
    let microcredits = match state.get(&Identifier::from_str("microcredits")?) {
        Some(Plaintext::Literal(Literal::U64(microcredits), _)) => **microcredits,
        _ => bail!("`microcredits` not found for: {address}"),
    };

    Ok(Some((validator, microcredits)))
}

fn initialize_arc_38_mappings<N: Network, F: FinalizeStorage<N>>(
    finalize_store: &FinalizeStore<N, F>,
) {
    // Initialize the store for 'arc_0038'.
    let (_, program) = Program::<N>::parse(arc_38_program()).unwrap();
    for mapping in program.mappings().values() {
        // Ensure that all mappings are initialized.
        if !finalize_store.contains_mapping_confirmed(program.id(), mapping.name()).unwrap() {
            // Initialize the mappings for 'arc_0038'.
            finalize_store.initialize_mapping(*program.id(), *mapping.name()).unwrap();
        }
    }
}

fn set_up_arc_38_test<N: Network, F: FinalizeStorage<N>>(
    rng: &mut TestRng,
    store:  &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    validator_num: u32,
) -> Result<(
    IndexMap<PrivateKey<CurrentNetwork>, (Address<CurrentNetwork>, u64)>,
    IndexMap<PrivateKey<CurrentNetwork>, (Address<CurrentNetwork>, u64)>,
   
    Process<CurrentNetwork>)> {
    // Construct the process.
    let (string, program) = Program::<CurrentNetwork>::parse(arc_38_program()).unwrap();
    assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
    let process = crate::test_helpers::sample_process(&program);

    // Initialize a new finalize store.
    // let (store, _temp_dir) = sample_finalize_store!();

    // Initialize the validators and delegators
    let (validators, delegators) = initialize_stakers(&store, validator_num, 1, rng, Some(ADMIN_PK())).unwrap();
    initialize_arc_38_mappings(&store);
    let mut validator_set = validators.clone().into_iter();

    // Bond the validators.
    let validator_amount = MIN_VALIDATOR_STAKE;
    for _ in 0..validator_num {
        let (validator_private_key, (validator_address, _)) = validator_set.next().unwrap();
        bond_public(&process, &store, &validator_private_key, &validator_address, &validator_address, validator_amount, rng).unwrap();
    }

    Ok((validators, delegators, process))
}

/// Initializes the validator and delegator balances in the finalize store.
/// Returns the private keys and balances for the validators and delegators.
fn initialize_stakers<N: Network, F: FinalizeStorage<N>>(
    finalize_store: &FinalizeStore<N, F>,
    num_validators: u32,
    num_delegators: u32,
    rng: &mut TestRng,
    admin_pk: Option<PrivateKey<N>>
) -> Result<(IndexMap<PrivateKey<N>, (Address<N>, u64)>, IndexMap<PrivateKey<N>, (Address<N>, u64)>)> {
    // Initialize the store for 'credits.aleo'.
    let program = Program::<N>::credits()?;
    for mapping in program.mappings().values() {
        // Ensure that all mappings are initialized.
        if !finalize_store.contains_mapping_confirmed(program.id(), mapping.name())? {
            // Initialize the mappings for 'credits.aleo'.
            finalize_store.initialize_mapping(*program.id(), *mapping.name())?;
        }
    }

    let mapping = Identifier::from_str("account")?;

    let mut validators: IndexMap<_, _> = Default::default();
    let mut delegators: IndexMap<_, _> = Default::default();

    // Initialize the balances for the validators and delegators.
    for i in 0..(num_validators + num_delegators) {
        // Initialize a new account.
        let private_key = PrivateKey::<N>::new(rng)?;
        let address = Address::try_from(&private_key)?;
        let balance = 10_000_000_000_000u64;

        // Add the balance directly to the finalize store.
        let key = Plaintext::from(Literal::Address(address));
        let value = Value::from(Literal::U64(U64::new(balance)));
        finalize_store.insert_key_value(*program.id(), mapping, key, value)?;
        assert_eq!(balance, account_balance(finalize_store, &address).unwrap());

        // Store the validator or delegator.
        if i < num_validators {
            // Insert the validator into the list of validators.
            validators.insert(private_key, (address, balance));
        } else {
            // Insert the delegator into the list of delegators.
            delegators.insert(private_key, (address, balance));
        }
    }

    if let Some(admin_pk) = admin_pk {
        // Initialize the admin account.
        let address = Address::try_from(&admin_pk)?;
        let balance = 10_000_000_000_000u64;

        // Add the balance directly to the finalize store.
        let key = Plaintext::from(Literal::Address(address));
        let value = Value::from(Literal::U64(U64::new(balance)));
        finalize_store.insert_key_value(*program.id(), mapping, key, value)?;
        assert_eq!(balance, account_balance(finalize_store, &address).unwrap());
    }

    Ok((validators, delegators))
}

fn execute_function<F: FinalizeStorage<CurrentNetwork>>(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, F>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    function: &str,
    inputs: &[String],
    block_height: Option<u32>,
    rng: &mut TestRng,
) -> Result<()> {
    // Construct the authorization.
    let authorization =
        process.authorize::<CurrentAleo, _>(caller_private_key, "credits.aleo", function, inputs.iter(), rng)?;

    // Construct the trace.
    let (_, mut trace) = process.execute::<CurrentAleo, _>(authorization, rng)?;

    // Construct the block store.
    let block_store = BlockStore::<CurrentNetwork, BlockMemory<_>>::open(None)?;

    // Prepare the trace.
    trace.prepare(Query::from(&block_store))?;

    // Prove the execution.
    let execution = trace.prove_execution::<CurrentAleo, _>(function, rng)?;

    // Finalize the execution.
    let block_height = block_height.unwrap_or(1);

    // Add an atomic finalize wrapper around the finalize function.
    process.finalize_execution(sample_finalize_state(block_height), finalize_store, &execution, None)?;

    Ok(())
}

fn execute_arc_38_function<F: FinalizeStorage<CurrentNetwork>>(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, F>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    function: &str,
    inputs: &[String],
    block_height: Option<u32>,
    rng: &mut TestRng,
) -> Result<()> {
    // Construct the authorization.
    let authorization =
        process.authorize::<CurrentAleo, _>(caller_private_key, "arc_0038.aleo", function, inputs.iter(), rng)?;

    // Construct the trace.
    let (_, mut trace) = process.execute::<CurrentAleo, _>(authorization, rng)?;

    // Construct the block store.
    let block_store = BlockStore::<CurrentNetwork, BlockMemory<_>>::open(None)?;

    // Prepare the trace.
    trace.prepare(Query::from(&block_store))?;

    // Prove the execution.
    let execution = trace.prove_execution::<CurrentAleo, _>(function, rng)?;

    // Finalize the execution.
    let block_height = block_height.unwrap_or(1);

    // Add an atomic finalize wrapper around the finalize function.
    process.finalize_execution(sample_finalize_state(block_height), finalize_store, &execution, None)?;

    Ok(())
}

/// Perform a `bond_public`.
fn bond_public<F: FinalizeStorage<CurrentNetwork>>(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, F>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    validator_address: &Address<CurrentNetwork>,
    withdrawal_address: &Address<CurrentNetwork>,
    amount: u64,
    rng: &mut TestRng,
) -> Result<()> {
    execute_function(
        process,
        finalize_store,
        caller_private_key,
        "bond_public",
        &[validator_address.to_string(), withdrawal_address.to_string(), format!("{amount}_u64")],
        None,
        rng,
    )
}

/// Perform an `unbond_public`.
fn unbond_public<F: FinalizeStorage<CurrentNetwork>>(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, F>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    amount: u64,
    block_height: u32,
    rng: &mut TestRng,
) -> Result<()> {
    execute_function(
        process,
        finalize_store,
        caller_private_key,
        "unbond_public",
        &[format!("{amount}_u64")],
        Some(block_height),
        rng,
    )
}

/// Perform an `unbond_delegator_as_validator`
fn unbond_delegator_as_validator<F: FinalizeStorage<CurrentNetwork>>(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, F>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    delegator_address: &Address<CurrentNetwork>,
    rng: &mut TestRng,
) -> Result<()> {
    execute_function(
        process,
        finalize_store,
        caller_private_key,
        "unbond_delegator_as_validator",
        &[delegator_address.to_string()],
        None,
        rng,
    )
}

fn initialize<F: FinalizeStorage<CurrentNetwork>>(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, F>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    commission_rate: u128,
    validator_address: &Address<CurrentNetwork>,
    rng: &mut TestRng,
) -> Result<()> {
    execute_arc_38_function(
        process,
        finalize_store,
        caller_private_key,
        "initialize",
        &[format!("{commission_rate}_u128"), validator_address.to_string()],
        None,
        rng
    )
}

fn initial_deposit<F: FinalizeStorage<CurrentNetwork>>(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, F>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    microcredits: u64,
    validator_address: &Address<CurrentNetwork>,
    rng: &mut TestRng,
) -> Result<()> {
    execute_arc_38_function(
        process,
        finalize_store,
        caller_private_key,
        "initial_deposit",
        &[format!("{microcredits}_u64"), validator_address.to_string()],
        None,
        rng
    )
}

fn set_commission_percent(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    commission_percent: u128,
    rng: &mut TestRng,
) -> Result<()> {
    execute_arc_38_function(
        process,
        finalize_store,
        caller_private_key,
        "set_commission_percent",
        &[format!("{commission_percent}_u128")],
        None,
        rng
    )
}

fn set_next_validator(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    validator_address: &Address<CurrentNetwork>,
    rng: &mut TestRng,
) -> Result<()> {
    execute_arc_38_function(
        process,
        finalize_store,
        caller_private_key,
        "set_next_validator",
        &[validator_address.to_string()],
        None,
        rng
    )
}

fn unbond_all(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    pool_balance: u64,
    rng: &mut TestRng,
) -> Result<()> {
    execute_arc_38_function(
        process,
        finalize_store,
        caller_private_key,
        "unbond_all",
        &[format!("{pool_balance}_u64")],
        None,
        rng
    )
}

fn claim_unbond(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    block_height: u32,
    rng: &mut TestRng,
) -> Result<()> {
    execute_arc_38_function(
        process,
        finalize_store,
        caller_private_key,
        "claim_unbond",
        &[],
        Some(block_height),
        rng
    )
}

fn bond_all(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    validator_address: &Address<CurrentNetwork>,
    pool_balance: u64,
    rng: &mut TestRng,
) -> Result<()> {
    execute_arc_38_function(
        process,
        finalize_store,
        caller_private_key,
        "bond_all",
        &[validator_address.to_string(), format!("{pool_balance}_u64")],
        None,
        rng
    )
}

fn bond_deposits(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    validator_address: &Address<CurrentNetwork>,
    amount: u64,
    rng: &mut TestRng,
) -> Result<()> {
    execute_arc_38_function(
        process,
        finalize_store,
        caller_private_key,
        "bond_deposits",
        &[validator_address.to_string(), format!("{amount}_u64")],
        None,
        rng
    )
}

fn claim_commission(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    rng: &mut TestRng,
) -> Result<()> {
    execute_arc_38_function(
        process,
        finalize_store,
        caller_private_key,
        "claim_commission",
        &[],
        None,
        rng
    )
}

fn deposit_public(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    amount: u64,
    rng: &mut TestRng,
) -> Result<()> {
    execute_arc_38_function(
        process,
        finalize_store,
        caller_private_key,
        "deposit_public",
        &[format!("{amount}_u64")],
        None,
        rng
    )
}

fn withdraw_public(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    withdrawal_shares: u64,
    total_withdrawal: u64,
    block_height: u32,
    rng: &mut TestRng,
) -> Result<()> {
    execute_arc_38_function(
        process,
        finalize_store,
        caller_private_key,
        "withdraw_public",
        &[format!("{withdrawal_shares}_u64"), format!("{total_withdrawal}_u64")],
        Some(block_height),
        rng
    )
}

fn create_withdraw_claim(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    withdrawal_shares: u64,
    rng: &mut TestRng,
) -> Result<()> {
    execute_arc_38_function(
        process,
        finalize_store,
        caller_private_key,
        "create_withdraw_claim",
        &[format!("{withdrawal_shares}_u64")],
        None,
        rng
    )
}

fn claim_withdrawal_public(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    recipient: &Address<CurrentNetwork>,
    amount: u64,
    block_height: u32,
    rng: &mut TestRng,
) -> Result<()> {
    execute_arc_38_function(
        process,
        finalize_store,
        caller_private_key,
        "claim_withdrawal_public",
        &[recipient.to_string(), format!("{amount}_u64")],
        Some(block_height),
        rng
    )
}

#[test]
fn test_get_commission() {
    let cases = vec![
        ("1u128", "1_000u128", "1u64", "100% commission of 1u128 reward"),
        ("1_000u128", "500u128", "500u64", "50% commission of 1_000u128 reward"),
        ("1_001u128", "500u128", "500u64", "50% commission of 1_001u128 reward"),
        ("59_987u128", "371u128", "22_255u64", "37.1% commission of 59_987u128 reward")
    ];
    for (r0_input, r1_input, expected, test_name) in cases {
        let (string, program) = Program::<CurrentNetwork>::parse(arc_38_program()).unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        let process = crate::test_helpers::sample_process(&program);
        let function_name = "get_commission_test";
    
        let rng = &mut TestRng::default();
    
        // Initialize caller private key.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
    
        let r0 = Value::<CurrentNetwork>::from_str(r0_input).unwrap();
        let r1 = Value::<CurrentNetwork>::from_str(r1_input).unwrap();
    
        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(&caller_private_key, program.id(), function_name, [r0, r1].iter(), rng)
            .unwrap();
        assert_eq!(authorization.len(), 1);
    
        let r4 = Value::<CurrentNetwork>::from_str(expected).unwrap();
    
        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(authorization.replicate()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(r4, candidate[0]);
    
        // Execute the request.
        let (response, _trace) = process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(r4, candidate[0], "{}", test_name);
    }
}

#[test]
fn test_initialize_success() {
    let rng = &mut TestRng::default();
    // Initialize a new finalize store.
    let (store, _temp_dir) = sample_finalize_store!();
    let (validators, delegators, process) = set_up_arc_38_test::<CurrentNetwork, FinalizeMemory<CurrentNetwork>>(rng, &store, 1).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();

    /* Ensure bonding a delegator with the exact MIN_DELEGATOR_STAKE succeeds. */
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        initialize(&process, &store, &ADMIN_PK(), 100u128, validator_address, rng).unwrap();

        // Check that the initialized mappings are set.
        let commission_rate = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "commission_percent",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(commission_rate, Some(Value::from_str("100u128").unwrap()));
        let set_validator = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "validator",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(set_validator, Some(Value::from_str(&validator_address.to_string()).unwrap()));
        let is_initialized = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "is_initialized",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(is_initialized, Some(Value::from_str("true").unwrap()));
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_initialize_fails() {
    let rng = &mut TestRng::default();
    // Initialize a new finalize store.
    let (store, _temp_dir) = sample_finalize_store!();
    let (validators, delegators, process) = set_up_arc_38_test::<CurrentNetwork, FinalizeMemory<CurrentNetwork>>(rng, &store, 1).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();

    let cases = vec![
        (1_000u128, ADMIN_PK().clone(), validator_address, "Commission rate 100%, too high"),
        (501u128, ADMIN_PK().clone(), validator_address, "Commission rate 50.1%, too high"),
        (20u128, delegator_private_key.clone(), validator_address, "Caller isn't the admin"),
    ];
    for (init_commission_rate, caller_private_key, init_validator_address, test_name) in cases {
        test_atomic_finalize!(store, FinalizeMode::RealRun, {
            let result = initialize(&process, &store, &caller_private_key, init_commission_rate, init_validator_address, rng);
            assert!(result.is_err(), "{}", test_name);
            Ok(())
        })
        .unwrap();
    }
}

#[test]
fn test_initial_deposit() {
    let rng = &mut TestRng::default();
    // Initialize a new finalize store.
    let (store, _temp_dir) = sample_finalize_store!();
    let (validators, delegators, process) = set_up_arc_38_test::<CurrentNetwork, FinalizeMemory<CurrentNetwork>>(rng, &store, 1).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();

    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        initialize(&process, &store, &ADMIN_PK(), 100u128, validator_address, rng).unwrap();

        // Check that the initialized mappings are set.
        let commission_rate = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "commission_percent",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(commission_rate, Some(Value::from_str("100u128").unwrap()));
        let set_validator = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "validator",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(set_validator, Some(Value::from_str(&validator_address.to_string()).unwrap()));
        let is_initialized = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "is_initialized",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(is_initialized, Some(Value::from_str("true").unwrap()));

        initial_deposit(&process, &store, &ADMIN_PK(), 10_000_000_000u64, validator_address, rng).unwrap();

        // Check that the initial deposit mappings are set.
        let total_balance = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_balance",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_balance, Some(Value::from_str("10_000_000_000u64").unwrap()));
        let total_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_shares",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_shares, Some(Value::from_str("10_000_000_000_000u64").unwrap()));
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_initial_deposit_fails() {
    let rng = &mut TestRng::default();
    // Initialize a new finalize store.
    let (store, _temp_dir) = sample_finalize_store!();
    let (validators, delegators, process) = set_up_arc_38_test::<CurrentNetwork, FinalizeMemory<CurrentNetwork>>(rng, &store, 2).unwrap();
    let (validator_private_key1, (validator_address1, _)) = validators.first().unwrap();
    let (validator_private_key2, (validator_address2, _)) = validators.last().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();

    let cases = vec![
        (MIN_DELEGATOR_STAKE, ADMIN_PK().clone(), validator_address2, "Wrong validator address"),
        (MIN_DELEGATOR_STAKE - 1, ADMIN_PK().clone(), validator_address1, "Initial Deposit too low"),
        (MIN_DELEGATOR_STAKE, delegator_private_key.clone(), validator_address1, "Caller isn't the admin"),
    ];

    initialize(&process, &store, &ADMIN_PK(), 100u128, validator_address1, rng).unwrap();
    // Check that the initialized mappings are set.
    let commission_rate = get_mapping_value(
        &store,
        "arc_0038.aleo",
        "commission_percent",
        Literal::U8(U8::new(0u8))
    ).unwrap();
    assert_eq!(commission_rate, Some(Value::from_str("100u128").unwrap()));
    let set_validator = get_mapping_value(
        &store,
        "arc_0038.aleo",
        "validator",
        Literal::U8(U8::new(0u8))
    ).unwrap();
    assert_eq!(set_validator, Some(Value::from_str(&validator_address1.to_string()).unwrap()));
    let is_initialized = get_mapping_value(
        &store,
        "arc_0038.aleo",
        "is_initialized",
        Literal::U8(U8::new(0u8))
    ).unwrap();
    assert_eq!(is_initialized, Some(Value::from_str("true").unwrap()));

    for (deposit_amount, caller_private_key, deposit_validator_address, test_name) in cases {
        test_atomic_finalize!(store, FinalizeMode::RealRun, {
            let result = initial_deposit(&process, &store, &caller_private_key, deposit_amount, deposit_validator_address, rng);
            assert!(result.is_err(), "{}", test_name);
            // Check that the initial deposit mappings are not set.
            let total_balance = get_mapping_value(
                &store,
                "arc_0038.aleo",
                "total_balance",
                Literal::U8(U8::new(0u8))
            ).unwrap();
            assert_eq!(total_balance, Some(Value::from_str("0u64").unwrap()), "Total balance is 0 {}", test_name);
            let total_shares = get_mapping_value(
                &store,
                "arc_0038.aleo",
                "total_shares",
                Literal::U8(U8::new(0u8))
            ).unwrap();
            assert_eq!(total_shares, Some(Value::from_str("0u64").unwrap()), "Total shares is 0 {}", test_name);
            Ok(())
        })
        .unwrap();
    }
}

#[test]
fn test_set_commission_percent() {
    let rng = &mut TestRng::default();
    // Initialize a new finalize store.
    let (store, _temp_dir) = sample_finalize_store!();
    let (validators, delegators, process) = set_up_arc_38_test::<CurrentNetwork, FinalizeMemory<CurrentNetwork>>(rng, &store, 1).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();

    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        initialize(&process, &store, &ADMIN_PK(), 100u128, validator_address, rng).unwrap();

        initial_deposit(&process, &store, &ADMIN_PK(), 10_000_000_000u64, validator_address, rng).unwrap();

        // Check that the initial deposit mappings are set.
        let total_balance = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_balance",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_balance, Some(Value::from_str("10_000_000_000u64").unwrap()));
        let total_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_shares",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_shares, Some(Value::from_str("10_000_000_000_000u64").unwrap()));

        add_rewards_to_bonded_state(&store, &PROTOCOL_ADDRESS(), 24_000_000u64).unwrap();

        set_commission_percent(&process, &store, &ADMIN_PK(), 50u128, rng).unwrap();

        // Check that the initialized mappings are set.
        let commission_rate = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "commission_percent",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(commission_rate, Some(Value::from_str("50u128").unwrap()));
        // Check that the rewards are added to the total balance.
        let total_balance = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_balance",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_balance, Some(Value::from_str("10_024_000_000u64").unwrap()));
        // Check that the validator shares have increased.
        let total_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_shares",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_shares, Some(Value::from_str("10_002_394_827_173u64").unwrap()));

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_set_next_validator() {
    let rng = &mut TestRng::default();
    // Initialize a new finalize store.
    let (store, _temp_dir) = sample_finalize_store!();
    let (validators, delegators, process) = set_up_arc_38_test::<CurrentNetwork, FinalizeMemory<CurrentNetwork>>(rng, &store, 2).unwrap();
    let (validator_private_key1, (validator_address1, _)) = validators.first().unwrap();
    let (validator_private_key2, (validator_address2, _)) = validators.last().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();

    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        set_next_validator(&process, &store, &ADMIN_PK(), validator_address1, rng).unwrap();

        // Check that the validator 1u8 mapping is set
        let next_validator = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "validator",
            Literal::U8(U8::new(1u8))
        ).unwrap();
        assert_eq!(next_validator, Some(Value::from_str(&validator_address1.to_string()).unwrap()));
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_unbond_all() {
    let rng = &mut TestRng::default();
    // Initialize a new finalize store.
    let (store, _temp_dir) = sample_finalize_store!();
    let (validators, delegators, process) = set_up_arc_38_test::<CurrentNetwork, FinalizeMemory<CurrentNetwork>>(rng, &store, 2).unwrap();
    let (validator_private_key1, (validator_address1, _)) = validators.first().unwrap();
    let (validator_private_key2, (validator_address2, _)) = validators.last().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        initialize(&process, &store, &ADMIN_PK(), 100u128, validator_address1, rng).unwrap();
        initial_deposit(&process, &store, &ADMIN_PK(), 10_000_000_000u64, validator_address1, rng).unwrap();
        set_next_validator(&process, &store, &ADMIN_PK(), validator_address2, rng).unwrap();
        add_rewards_to_bonded_state(&store, &PROTOCOL_ADDRESS(), 24_000_000u64).unwrap();
        unbond_all(&process, &store, &ADMIN_PK(), 10_000_000_000u64, rng).unwrap();

        // Check that the rewards are added to the total balance.
        let total_balance = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_balance",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_balance, Some(Value::from_str("10_024_000_000u64").unwrap()));
        // Check that the total shares have increased.
        let total_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_shares",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_shares, Some(Value::from_str("10_002_394_827_173u64").unwrap()));
        // Check the validator shares have increased.
        let total_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "delegator_shares",
            Literal::Address(ADMIN_PUB_KEY())
        ).unwrap();
        assert_eq!(total_shares, Some(Value::from_str("10_002_394_827_173u64").unwrap()));
        // Check that the unbond_state is set
        assert_eq!(unbond_state(&store, &PROTOCOL_ADDRESS()).unwrap(), Some((10_024_000_000u64, 361)));
        // Check that the bond state is zero
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_claim_unbond() {
    let rng = &mut TestRng::default();
    // Initialize a new finalize store.
    let (store, _temp_dir) = sample_finalize_store!();
    let (validators, delegators, process) = set_up_arc_38_test::<CurrentNetwork, FinalizeMemory<CurrentNetwork>>(rng, &store, 2).unwrap();
    let (validator_private_key1, (validator_address1, _)) = validators.first().unwrap();
    let (validator_private_key2, (validator_address2, _)) = validators.last().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        initialize(&process, &store, &ADMIN_PK(), 100u128, validator_address1, rng).unwrap();
        initial_deposit(&process, &store, &ADMIN_PK(), 10_000_000_000u64, validator_address1, rng).unwrap();
        set_next_validator(&process, &store, &ADMIN_PK(), validator_address2, rng).unwrap();
        add_rewards_to_bonded_state(&store, &PROTOCOL_ADDRESS(), 24_000_000u64).unwrap();
        unbond_all(&process, &store, &ADMIN_PK(), 10_000_000_000u64, rng).unwrap();
        claim_unbond(&process, &store, &ADMIN_PK(), 361, rng).unwrap();

        // Check account balance is fully claimed to the protocol
        let protocol_balance = account_balance(&store, &PROTOCOL_ADDRESS()).unwrap();
        assert_eq!(protocol_balance, 10_024_000_000u64);
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_bond_all() {
    let rng = &mut TestRng::default();
    // Initialize a new finalize store.
    let (store, _temp_dir) = sample_finalize_store!();
    let (validators, delegators, process) = set_up_arc_38_test::<CurrentNetwork, FinalizeMemory<CurrentNetwork>>(rng, &store, 2).unwrap();
    let (validator_private_key1, (validator_address1, _)) = validators.first().unwrap();
    let (validator_private_key2, (validator_address2, _)) = validators.last().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        initialize(&process, &store, &ADMIN_PK(), 100u128, validator_address1, rng).unwrap();
        initial_deposit(&process, &store, &ADMIN_PK(), 10_000_000_000u64, validator_address1, rng).unwrap();
        set_next_validator(&process, &store, &ADMIN_PK(), validator_address2, rng).unwrap();
        add_rewards_to_bonded_state(&store, &PROTOCOL_ADDRESS(), 24_000_000u64).unwrap();
        unbond_all(&process, &store, &ADMIN_PK(), 10_000_000_000u64, rng).unwrap();
        claim_unbond(&process, &store, &ADMIN_PK(), 361, rng).unwrap();
        bond_all(&process, &store, &ADMIN_PK(), validator_address2, 10_024_000_000u64, rng).unwrap();

        // check the bond state
        assert_eq!(bond_state(&store, &PROTOCOL_ADDRESS()).unwrap(), Some((*validator_address2, 10_024_000_000u64)));
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_bond_all_fails_for_invalid_validator() {
    let rng = &mut TestRng::default();
    // Initialize a new finalize store.
    let (store, _temp_dir) = sample_finalize_store!();
    let (validators, delegators, process) = set_up_arc_38_test::<CurrentNetwork, FinalizeMemory<CurrentNetwork>>(rng, &store, 2).unwrap();
    let (validator_private_key1, (validator_address1, _)) = validators.first().unwrap();
    let (validator_private_key2, (validator_address2, _)) = validators.last().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        initialize(&process, &store, &ADMIN_PK(), 100u128, validator_address1, rng).unwrap();
        initial_deposit(&process, &store, &ADMIN_PK(), 10_000_000_000u64, validator_address1, rng).unwrap();
        set_next_validator(&process, &store, &ADMIN_PK(), validator_address2, rng).unwrap();
        add_rewards_to_bonded_state(&store, &PROTOCOL_ADDRESS(), 24_000_000u64).unwrap();
        unbond_all(&process, &store, &ADMIN_PK(), 10_000_000_000u64, rng).unwrap();
        claim_unbond(&process, &store, &ADMIN_PK(), 361, rng).unwrap();

        // not a validator
        set_next_validator(&process, &store, &ADMIN_PK(), delegator_address, rng).unwrap();
        let result = bond_all(&process, &store, &ADMIN_PK(), validator_address2, 10_024_000_000u64, rng);
        assert!(result.is_err(), "{}", "Bonding to a non-validator should fail");

        // check the bond state
        assert_eq!(bond_state(&store, &PROTOCOL_ADDRESS()).unwrap(), None);
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_claim_commission() {
    let rng = &mut TestRng::default();
    // Initialize a new finalize store.
    let (store, _temp_dir) = sample_finalize_store!();
    let (validators, delegators, process) = set_up_arc_38_test::<CurrentNetwork, FinalizeMemory<CurrentNetwork>>(rng, &store, 1).unwrap();
    let (validator_private_key1, (validator_address1, _)) = validators.first().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        initialize(&process, &store, &ADMIN_PK(), 100u128, validator_address1, rng).unwrap();
        initial_deposit(&process, &store, &ADMIN_PK(), 10_000_000_000u64, validator_address1, rng).unwrap();
        add_rewards_to_bonded_state(&store, &PROTOCOL_ADDRESS(), 24_000_000u64).unwrap();
        claim_commission(&process, &store, &ADMIN_PK(), rng).unwrap();

        // Check that the rewards are added to the total balance.
        let total_balance = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_balance",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_balance, Some(Value::from_str("10_024_000_000u64").unwrap()));
        // Check that the total shares have increased.
        let total_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_shares",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_shares, Some(Value::from_str("10_002_394_827_173u64").unwrap()));
        // Check the admin shares have increased.
        let admin_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "delegator_shares",
            Literal::Address(ADMIN_PUB_KEY())
        ).unwrap();
        assert_eq!(admin_shares, Some(Value::from_str("10_002_394_827_173u64").unwrap()));
        
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_deposit_public() {
    let rng = &mut TestRng::default();
    // Initialize a new finalize store.
    let (store, _temp_dir) = sample_finalize_store!();
    let (validators, delegators, process) = set_up_arc_38_test::<CurrentNetwork, FinalizeMemory<CurrentNetwork>>(rng, &store, 1).unwrap();
    let (validator_private_key1, (validator_address1, _)) = validators.first().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        initialize(&process, &store, &ADMIN_PK(), 100u128, validator_address1, rng).unwrap();
        initial_deposit(&process, &store, &ADMIN_PK(), 10_000_000_000u64, validator_address1, rng).unwrap();
        deposit_public(&process, &store, delegator_private_key, 10_000_000_000u64, rng).unwrap();

        // Check the admin shares have not increased.
        let admin_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "delegator_shares",
            Literal::Address(ADMIN_PUB_KEY())
        ).unwrap();
        assert_eq!(admin_shares, Some(Value::from_str("10_000_000_000_000u64").unwrap()));
        // Check the total balance has not increased.
        let total_balance = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_balance",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_balance, Some(Value::from_str("10_000_000_000u64").unwrap()));
        // Check the pending deposits has increased.
        let pending_deposits = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "pending_deposits",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(pending_deposits, Some(Value::from_str("10_000_000_000u64").unwrap()));
        // Check the total shares have increased.
        let total_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_shares",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_shares, Some(Value::from_str("20_000_000_000_000u64").unwrap()));
        // Check that the depositor shares have increased.
        let delegator_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "delegator_shares",
            Literal::Address(*delegator_address)
        ).unwrap();
        assert_eq!(delegator_shares, Some(Value::from_str("10_000_000_000_000u64").unwrap()));
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_deposit_public_fails() {
    let rng = &mut TestRng::default();
    // Initialize a new finalize store.
    let (store, _temp_dir) = sample_finalize_store!();
    let (validators, delegators, process) = set_up_arc_38_test::<CurrentNetwork, FinalizeMemory<CurrentNetwork>>(rng, &store, 1).unwrap();
    let (validator_private_key1, (validator_address1, _)) = validators.first().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();

    // initialize(&process, &store, &ADMIN_PK(), 100u128, validator_address1, rng).unwrap();
    // initial_deposit(&process, &store, &ADMIN_PK(), 10_000_000_000_000u64, validator_address1, rng).unwrap();
    let cases = vec![
        (0u64, delegator_private_key.clone(), "Depositing 0 microcredits fails"),
    ];
    for (deposit_amount, caller_private_key, test_name) in cases {
        test_atomic_finalize!(store, FinalizeMode::RealRun, {
            initialize(&process, &store, &ADMIN_PK(), 100u128, validator_address1, rng).unwrap();
            initial_deposit(&process, &store, &ADMIN_PK(), 10_000_000_000_000u64, validator_address1, rng).unwrap();
            let result = deposit_public(&process, &store, &caller_private_key, deposit_amount, rng);
            assert!(result.is_err(), "{}", test_name);
            Ok(())
        })
        .unwrap();
    }
}

#[test]
fn test_bond_deposits() {
    let rng = &mut TestRng::default();
    // Initialize a new finalize store.
    let (store, _temp_dir) = sample_finalize_store!();
    let (validators, delegators, process) = set_up_arc_38_test::<CurrentNetwork, FinalizeMemory<CurrentNetwork>>(rng, &store, 1).unwrap();
    let (validator_private_key1, (validator_address1, _)) = validators.first().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        initialize(&process, &store, &ADMIN_PK(), 100u128, validator_address1, rng).unwrap();
        initial_deposit(&process, &store, &ADMIN_PK(), 10_000_000_000u64, validator_address1, rng).unwrap();
        deposit_public(&process, &store, delegator_private_key, 10_000_000_000u64, rng).unwrap();
        bond_deposits(&process, &store, delegator_private_key, validator_address1, 10_000_000_000u64, rng).unwrap();

        // Check the admin shares have not increased.
        let admin_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "delegator_shares",
            Literal::Address(ADMIN_PUB_KEY())
        ).unwrap();
        assert_eq!(admin_shares, Some(Value::from_str("10_000_000_000_000u64").unwrap()));
        // Check the total balance accounts for all the deposits
        let total_balance = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_balance",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_balance, Some(Value::from_str("20_000_000_000u64").unwrap()));
        // Check the pending deposits is 0.
        let pending_deposits = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "pending_deposits",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(pending_deposits, Some(Value::from_str("0u64").unwrap()));
        // Check the total shares have increased.
        let total_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_shares",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_shares, Some(Value::from_str("20_000_000_000_000u64").unwrap()));
        // Check that the depositor shares have increased.
        let delegator_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "delegator_shares",
            Literal::Address(*delegator_address)
        ).unwrap();
        assert_eq!(delegator_shares, Some(Value::from_str("10_000_000_000_000u64").unwrap()));
        // Check the bond state
        assert_eq!(bond_state(&store, &PROTOCOL_ADDRESS()).unwrap(), Some((*validator_address1, 20_000_000_000u64)));

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_bond_deposits_fails_on_direct_credit_transfer_but_before_initial_deposit() {
    let rng = &mut TestRng::default();
    // Initialize a new finalize store.
    let (store, _temp_dir) = sample_finalize_store!();
    let (validators, delegators, process) = set_up_arc_38_test::<CurrentNetwork, FinalizeMemory<CurrentNetwork>>(rng, &store, 1).unwrap();
    let (validator_private_key1, (validator_address1, _)) = validators.first().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        initialize(&process, &store, &ADMIN_PK(), 100u128, validator_address1, rng).unwrap();
        execute_function(&process, &store, delegator_private_key, "transfer_public", &[String::from("arc_0038.aleo"), String::from("5000u64")], None, rng).unwrap();
        let result = bond_deposits(&process, &store, delegator_private_key, validator_address1, 5000u64, rng);
        assert!(result.is_err(), "{}", "Bonding before initial deposit should fail");
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_withdraw_public() {
    let rng = &mut TestRng::default();
    // Initialize a new finalize store.
    let (store, _temp_dir) = sample_finalize_store!();
    let (validators, delegators, process) = set_up_arc_38_test::<CurrentNetwork, FinalizeMemory<CurrentNetwork>>(rng, &store, 1).unwrap();
    let (validator_private_key1, (validator_address1, _)) = validators.first().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        initialize(&process, &store, &ADMIN_PK(), 100u128, validator_address1, rng).unwrap();
        initial_deposit(&process, &store, &ADMIN_PK(), 10_000_000_000u64, validator_address1, rng).unwrap();
        deposit_public(&process, &store, delegator_private_key, 10_000_000_000u64, rng).unwrap();
        bond_deposits(&process, &store, delegator_private_key, validator_address1, 10_000_000_000u64, rng).unwrap();
        withdraw_public(&process, &store, delegator_private_key, 10_000_000_000_000u64, 10_000_000_000u64, 5u32, rng).unwrap();

        let admin_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "delegator_shares",
            Literal::Address(ADMIN_PUB_KEY())
        ).unwrap();
        assert_eq!(admin_shares, Some(Value::from_str("10_000_000_000_000u64").unwrap()), "Admin shares have not changed");
        // Check the total balance accounts for all the deposits
        let total_balance = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_balance",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_balance, Some(Value::from_str("10_000_000_000u64").unwrap()), "Total balance has decreased");
        let total_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_shares",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_shares, Some(Value::from_str("10_000_000_000_000u64").unwrap()), "Total shares have decreased");
        let delegator_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "delegator_shares",
            Literal::Address(*delegator_address)
        ).unwrap();
        assert_eq!(delegator_shares, Some(Value::from_str("0u64").unwrap()), "withdrawer shares have decreased");
        // Check the bond state
        assert_eq!(bond_state(&store, &PROTOCOL_ADDRESS()).unwrap(), Some((*validator_address1, 10_000_000_000u64)), "Bond state has decreased");

        assert_eq!(withdraw_state(&store, delegator_address).unwrap(), Some((10_000_000_000u64, 1000u32)), "Withdraw state has been set");
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_create_withdraw_claim() {

}

#[test]
fn test_claim_withdrawal_public() {
    let rng = &mut TestRng::default();
    // Initialize a new finalize store.
    let (store, _temp_dir) = sample_finalize_store!();
    let (validators, delegators, process) = set_up_arc_38_test::<CurrentNetwork, FinalizeMemory<CurrentNetwork>>(rng, &store, 1).unwrap();
    let (validator_private_key1, (validator_address1, _)) = validators.first().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        initialize(&process, &store, &ADMIN_PK(), 100u128, validator_address1, rng).unwrap();
        initial_deposit(&process, &store, &ADMIN_PK(), 10_000_000_000u64, validator_address1, rng).unwrap();
        deposit_public(&process, &store, delegator_private_key, 10_000_000_000u64, rng).unwrap();
        bond_deposits(&process, &store, delegator_private_key, validator_address1, 10_000_000_000u64, rng).unwrap();
        withdraw_public(&process, &store, delegator_private_key, 10_000_000_000_000u64, 10_000_000_000u64, 5u32, rng).unwrap();
        claim_unbond(&process, &store, delegator_private_key, 365u32, rng).unwrap();
        claim_withdrawal_public(&process, &store, delegator_private_key, delegator_address, 10_000_000_000u64, 1000u32, rng).unwrap();

        let admin_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "delegator_shares",
            Literal::Address(ADMIN_PUB_KEY())
        ).unwrap();
        assert_eq!(admin_shares, Some(Value::from_str("10_000_000_000_000u64").unwrap()), "Admin shares have not changed");
        // Check the total balance accounts for all the deposits
        let total_balance = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_balance",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_balance, Some(Value::from_str("10_000_000_000u64").unwrap()), "Total balance has decreased");
        let total_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "total_shares",
            Literal::U8(U8::new(0u8))
        ).unwrap();
        assert_eq!(total_shares, Some(Value::from_str("10_000_000_000_000u64").unwrap()), "Total shares have decreased");
        let delegator_shares = get_mapping_value(
            &store,
            "arc_0038.aleo",
            "delegator_shares",
            Literal::Address(*delegator_address)
        ).unwrap();
        assert_eq!(delegator_shares, Some(Value::from_str("0u64").unwrap()), "withdrawer shares have decreased");
        // Check the bond state
        assert_eq!(bond_state(&store, &PROTOCOL_ADDRESS()).unwrap(), Some((*validator_address1, 10_000_000_000u64)), "Bond state has decreased");

        // original delegator balance is 10_000_000_000_000u64 -- we're checking that this balance remains the same after bonding and then withdrawing
        assert_eq!(account_balance(&store, delegator_address).unwrap(), 10_000_000_000_000u64, "Recipient balance has increased");

        Ok(())
    })
    .unwrap();
}