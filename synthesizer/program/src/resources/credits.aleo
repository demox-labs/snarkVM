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

/**********************************************************************************************************************/

program credits.aleo;

/**********************************************************************************************************************/

/// The `committee` mapping contains the active validator set and their corresponding stake.
mapping committee:
    // The key represents the address of the validator.
    key as address.public;
    // The value represents the committee state of the validator.
    value as committee_state.public;

// The `committee_state` struct tracks the total stake of the validator, and whether they are open to new validators.
struct committee_state:
    // The amount of microcredits bonded to the validator, by the validator and its delegators.
    microcredits as u64;
    // The boolean flag indicating if the validator is open to new validators.
    is_open as boolean;

/**********************************************************************************************************************/

/// The `metadata` mapping stores:
///   - The number of members in the committee.
///   - The number of delegators.
mapping metadata:
    // The key represents the index at which the count is stored.
    //    - This address (aleo1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq3ljyzc) stores the number of **members** in the committee.
    key as address.public;
    // The value represents the count.
    value as u32.public;

/**********************************************************************************************************************/

// The `bonded` mapping represents the amount of microcredits that are currently bonded.
mapping bonded:
    // The key represents the address of the validator, which includes the validators and their delegators.
    key as address.public;
    // The value represents the bond state.
    value as bond_state.public;

// The `bond_state` struct tracks the amount of microcredits that are currently bonded to the specified validator.
struct bond_state:
    // The address of the validator.
    validator as address;
    // The amount of microcredits that are currently bonded to the specified validator.
    microcredits as u64;

/**********************************************************************************************************************/

// The `unbonding` mapping contains a set of validators with their unbonding microcredits and unlock height.
mapping unbonding:
    // The key represents the address of the validator, which includes the validators and their delegators.
    key as address.public;
    // The value represents the unbond state.
    value as unbond_state.public;

// The `unbond_state` struct tracks the microcredits that are currently unbonding, along with the unlock height.
struct unbond_state:
    // The amount of microcredits that are currently unbonding.
    microcredits as u64;
    // The block height at which the unbonding will be complete, and can be claimed.
    height as u32;

/**********************************************************************************************************************/

// The `account` mapping is used to store credits publicly.
mapping account:
    // The key represents the address of the owner.
    key as address.public;
    // The value represents the amount of public microcredits that belong to the specified owner.
    value as u64.public;

/**********************************************************************************************************************/

// The `control` mapping contains the validator address and their corresponding control address.
mapping control:
    // The key represents the validator address.
    key as address.public;
    // The value represents the control address of the owner.
    value as address.public;

/**********************************************************************************************************************/

// The `credits` record is used to store credits privately.
record credits:
    // The address of the owner.
    owner as address.private;
    // The amount of private microcredits that belong to the specified owner.
    microcredits as u64.private;

/**********************************************************************************************************************/

// This function allows any validator to bond their microcredits to a validator and specify a control address.
// The corresponding functions for 'bond_public' are 'unbond_public' and 'claim_unbond_public'.

function bond_validator_public:
    // Input the control address.
    input r0 as address.public; // Cold key or program
    // Input the amount of microcredits to bond.
    input r1 as u64.public; // Amount of microcredits to bond

    // Determine if the amount is at least one credit.
    gte r2 10_000_000_000_000u64 into r3;
    // Enforce the amount is at least one credit.
    assert.eq r3 true;

    // Bond the specified amount of microcredits to the specified validator.
    async bond_validator_public self.signer r0 r1 into r4;
    // Output the finalize future.
    output r4 as credits.aleo/bond_public.future;

finalize bond_validator_public:
    // Input the validator's address.
    input r0 as address.public; // Hot key worker address on validator node
    // Input the control address.
    input r1 as address.public; // Cold key or program
    // Input the amount of microcredits to bond.
    input r2 as u64.public; // Amount of microcredits to bond


function bond_public:
    // Input the validator's address.
    input r0 as address.public; // Hot key worker address on validator node
    // Input the control address.
    input r1 as address.public; // Cold key or program
    // Input the amount of microcredits to bond.
    input r2 as u64.public; // Amount of microcredits to bond

    // Determine if the amount is at least one credit.
    gte r2 1_000_000u64 into r3;
    // Enforce the amount is at least one credit.
    assert.eq r3 true;

    // Bond the specified amount of microcredits to the specified validator.
    async bond_public self.signer self.caller r0 r1 r2 into r4;
    // Output the finalize future.
    output r4 as credits.aleo/bond_public.future;

finalize bond_public:
    // Input the validator's address
    input r0 as address.public;
    // Input the caller's address.
    input r1 as address.public;
    // Input the validator's address.
    input r2 as address.public;
    // Input the control address.
    input r3 as address.public;
    // Input the amount of microcredits to bond.
    input r4 as u64.public;

    // Retrieve the control address for the validator.
    get.or_use control[r0] r1 into r5;
    // Ensure that the control address is consistent.
    assert.eq r1 r5;

    // Determine whether the caller is a validator.
    is.eq r1 r2 into r6;
    ternary r6 self.signer self.caller into r7;
    // If the caller is a validator, jump to the `bond_validator` logic.
    branch.eq r6 true to bond_validator;
    // If the caller is not a validator, jump to the `bond_delegator` logic.
    branch.eq r6 false to bond_delegator;

    /******* Bond Validator *******/

    // Starts the `bond_validator` logic.
    position bond_validator;

    /* Committee */

    // Check if the validator is already in the committee.
    contains committee[r7] into r8;
    // If the validator is already in the committee, jump to the `continue_bond_validator` logic.
    branch.eq r6 true to continue_bond_validator;

    // Get the committee size.
    get.or_use metadata[aleo1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq3ljyzc] 0u32 into r9;
    // Increment the committee size by one.
    add r9 1u32 into r10;
    // Set the new committee size.
    set r10 into metadata[aleo1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq3ljyzc];
    // Set the control address.
    set r3 into control[r7];

    // Continues the rest of the `bond_validator` logic.
    position continue_bond_validator;

    // Construct the initial committee state.
    // Note: We set the initial 'is_open' state to 'true'.
    cast 0u64 true into r11 as committee_state;
    // Retrieve the committee state of the specified validator.
    get.or_use committee[r7] r11 into r12;

    // Increment the stake for the specified validator.
    add r12.microcredits r4 into r13;
    // Construct the updated committee state.
    cast r13 r12.is_open into r14 as committee_state;

    /* Bonded */

    // Construct the initial bond state.
    cast r7 0u64 into r15 as bond_state;
    // Get the bond state for the caller, or default to the initial bond state.
    get.or_use bonded[r7] r15 into r16;
    // Enforce the validator matches in the bond state.
    assert.eq r16.validator r7;

    // Increment the microcredits in the bond state.
    add r16.microcredits r4 into r17;
    // Determine if the amount is at least 10 million credits.
    gte r17 10_000_000_000_000u64 into r18;
    // Enforce the amount is at least 10 million credits.
    assert.eq r18 true;

    // Construct the updated bond state.
    cast r7 r17 into r19 as bond_state;

    /* Account */

    // Get the balance of the caller.
    // If the account does not exist, this finalize scope will fail.
    get account[r7] into r20;
    // Decrement the balance of the caller.
    sub r20 r4 into r21;

    /* Writes */

    // Update the committee state of the specified validator.
    set r14 into committee[r7];
    // Update the bond state for the caller.
    set r19 into bonded[r7];
    // Update the balance of the caller.
    set r21 into account[r7];

    // The terminus.
    position end;

/**********************************************************************************************************************/

// This function allows any validator to unbond their microcredits from a validator.
// The corresponding function for 'unbond_public' is 'claim_unbond_public'.
function unbond_public:
    // Input the validator address
    input r0 as address.public;
    // Input the amount of microcredits to unbond.
    input r1 as u64.public;

    // Unbond the specified amount of microcredits to the caller.
    async unbond_public self.caller r0 r1 into r2;
    // Output the finalize future.
    output r2 as credits.aleo/unbond_public.future;

finalize unbond_public:
    // Input the control address (as self.caller)
    input r0 as address.public;
    // Input the validator's address
    input r1 as address.public;
    // Input the amount of microcredits to unbond.
    input r2 as u64.public;

    // Ensure that self.caller has the permission to unbond a specific validator
    get control[r1] into r3;
    assert.eq r0 r3;

    // Construct the initial unbond state.
    cast 0u64 0u32 into r3 as unbond_state;
    // Get the unbond state for the validator, or default to the initial unbond state.
    get.or_use unbonding[r1] r3 into r4;

    // Compute the height at which the unbonding will be complete, starting from the current block.
    // Note: Calling unbond across multiple blocks before the unbonding is complete will reset the height each time.
    add block.height 360u32 into r5;

    /******* Unbond Validator *******/

    /* Committee */

    // Get the committee state for the specified validator.
    get committee[r1] into r7;
    // Decrement the stake for the specified validator.
    sub r7.microcredits r2 into r8;

    /* Bonded */

    // Get the bond state for the validator, or fail if it does not exist.
    get bonded[r0] into r9;
    // Ensure that the validator matches in the bond state.
    assert.eq r9.validator r0;
    // Decrement the microcredits in the bond state.
    sub r9.microcredits r2 into r10;

    // Determine if the remaining bond is at least 10 million credits.
    gte r10 10_000_000_000_000u64 into r11;

    // If the remaining balance is at least 10 million credits, jump to the `decrement_validator` logic.
    branch.eq r11 true to decrement_validator;
    // If the remaining balance is less than 10 million credits, jump to the `remove_validator` logic.
    branch.eq r11 false to remove_validator;

    /*** Decrement Validator ***/

    // Starts the `decrement_validator` logic.
    position decrement_validator;

    /* Committee */

    // Construct the updated committee state.
    cast r8 r7.is_open into r12 as committee_state;
    // Update the committee state for the validator.
    set r12 into committee[r0];

    /* Bonded */

    // Construct the updated bond state.
    cast r0 r10 into r13 as bond_state;
    // Update the bond state for the validator.
    set r13 into bonded[r0];

    /* Unbonding */

    // Increment the microcredits in the unbond state.
    add r4.microcredits r2 into r14;

    // Construct the updated unbond state.
    cast r14 r5 into r15 as unbond_state;
    // Update the unbond state for the caller.
    set r15 into unbonding[r0];

    // Ends the `decrement_validator` logic.
    branch.eq true true to end;

    /*** Remove Validator ***/

    // Starts the `remove_validator` logic.
    position remove_validator;

    // Ensure that the validator has no delegators.
    assert.eq r7.microcredits r9.microcredits;

    /* Committee */

    // Remove the validator from the committee.
    remove committee[r0];

    // Get the committee size.
    get metadata[aleo1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq3ljyzc] into r16;
    // Decrement the committee size by one.
    sub r16 1u32 into r17;
    // Set the new committee size.
    set r17 into metadata[aleo1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq3ljyzc];

    /* Bonded */

    // Remove the bond state for the validator.
    remove bonded[r0];

    /* Unbonding */

    // Increment the microcredits in the unbond state.
    add r4.microcredits r9.microcredits into r18;

    // Construct the updated unbond state.
    cast r18 r5 into r19 as unbond_state;
    // Update the unbond state for the caller.
    set r19 into unbonding[r0];

    // The terminus.
    position end;

/**********************************************************************************************************************/


// The `claim_unbond_public` function allows any validator to claim their microcredits
// to their control address after the unbonding period.
//
// This function also removes the validator's control address if the validator no longer has any bonded balance.
function claim_unbond_public:
    input r0 as address.public;
    // Claim the unbonded microcredits.
    async claim_unbond_public r0 into r1;
    // Output the finalize future.
    output r1 as credits.aleo/claim_unbond_public.future;

finalize claim_unbond_public:
    // Input the validator's address.
    input r0 as address.public;

    // Get the unbond state for the validator, or fail if it does not exist.
    get unbonding[r0] into r1;
    // Determine if unbonding is complete.
    gte block.height r1.height into r2;
    // Enforce the unbonding is complete.
    assert.eq r2 true;

    // Get the control address for the validator.
    get control[r0] into r3;

    // Add the unbonded amount to the control address public balance.
    // Increments `account[r3]` by `r1`.
    // If `account[r3]` does not exist, 0u64 is used.
    // If `account[r3] + r1` overflows, `claim_unbond_public` is reverted.
    get.or_use account[r3] 0u64 into r4;
    add r1.microcredits r4 into r5;
    set r5 into account[r3];

    // Remove the unbond state for the validator.
    remove unbonding[r0];

    // Check if the validator is still bonded.
    contains bonded[r0] into r6;
    // Ends the `claim_unbond_public` logic.
    branch.eq r6 true to end;

    // If the validator is no longer bonded, remove the control address.
    remove control[r0];

    // The terminus.
    position end;


/**********************************************************************************************************************/

// The `transfer_public` function sends the specified amount
// from the caller's `account` to the receiver's `account`.
function transfer_public:
    // Input the receiver.
    input r0 as address.public;
    // Input the amount.
    input r1 as u64.public;
    // Transfer the credits publicly.
    async transfer_public self.caller r0 r1 into r2;
    // Output the finalize future.
    output r2 as credits.aleo/transfer_public.future;

finalize transfer_public:
    // Input the caller.
    input r0 as address.public;
    // Input the receiver.
    input r1 as address.public;
    // Input the amount.
    input r2 as u64.public;
    // Decrements `account[r0]` by `r2`.
    // If `account[r0] - r2` underflows, `transfer_public` is reverted.
    get account[r0] into r3;
    sub r3 r2 into r4;
    set r4 into account[r0];
    // Increments `account[r1]` by `r2`.
    // If `account[r1]` does not exist, 0u64 is used.
    // If `account[r1] + r2` overflows, `transfer_public` is reverted.
    get.or_use account[r1] 0u64 into r5;
    add r5 r2 into r6;
    set r6 into account[r1];

/**********************************************************************************************************************/

// The `transfer_public_as_signer` function sends the specified amount
// from the signer's `account` to the receiver's `account`.
function transfer_public_as_signer:
    // Input the receiver.
    input r0 as address.public;
    // Input the amount.
    input r1 as u64.public;
    // Transfer the credits publicly.
    async transfer_public_as_signer self.signer r0 r1 into r2;
    // Output the finalize future.
    output r2 as credits.aleo/transfer_public_as_signer.future;

finalize transfer_public_as_signer:
    // Input the signer.
    input r0 as address.public;
    // Input the receiver.
    input r1 as address.public;
    // Input the amount.
    input r2 as u64.public;
    // Decrements `account[r0]` by `r2`.
    // If `account[r0] - r2` underflows, `transfer_public_as_signer` is reverted.
    get account[r0] into r3;
    sub r3 r2 into r4;
    set r4 into account[r0];
    // Increments `account[r1]` by `r2`.
    // If `account[r1]` does not exist, 0u64 is used.
    // If `account[r1] + r2` overflows, `transfer_public_as_signer` is reverted.
    get.or_use account[r1] 0u64 into r5;
    add r5 r2 into r6;
    set r6 into account[r1];

/**********************************************************************************************************************/

// The `transfer_private` function sends the specified amount
// from the sender's record to the receiver in a record.
function transfer_private:
    // Input the sender's record.
    input r0 as credits.record;
    // Input the receiver.
    input r1 as address.private;
    // Input the amount.
    input r2 as u64.private;
    // Checks the given record has a sufficient amount.
    // This `sub` operation is safe, and the proof will fail
    // if an underflow occurs. The destination register `r3` holds
    // the change amount to be returned to the sender.
    sub r0.microcredits r2 into r3;
    // Construct a record for the specified receiver.
    cast r1 r2 into r4 as credits.record;
    // Construct a record with the change amount for the sender.
    cast r0.owner r3 into r5 as credits.record;
    // Output the receiver's record.
    output r4 as credits.record;
    // Output the sender's change record.
    output r5 as credits.record;

/**********************************************************************************************************************/

// The `transfer_private_to_public` function turns a specified amount
// from a record into public credits for the specified receiver.
//
// This function preserves privacy for the sender's record, however
// it publicly reveals the receiver and the amount.
function transfer_private_to_public:
    // Input the sender's record.
    input r0 as credits.record;
    // Input the receiver.
    input r1 as address.public;
    // Input the amount.
    input r2 as u64.public;
    // Checks the given record has a sufficient amount.
    // This `sub` operation is safe, and the proof will fail
    // if an underflow occurs. The destination register `r3` holds
    // the change amount for the sender.
    sub r0.microcredits r2 into r3;
    // Construct a record with the change amount for the sender.
    cast r0.owner r3 into r4 as credits.record;
    // Increment the amount publicly for the receiver.
    async transfer_private_to_public r1 r2 into r5;
    // Output the sender's change record.
    output r4 as credits.record;
    // Output the finalize future.
    output r5 as credits.aleo/transfer_private_to_public.future;

finalize transfer_private_to_public:
    // Input the receiver.
    input r0 as address.public;
    // Input the amount.
    input r1 as u64.public;
    // Retrieve the balance of the receiver.
    // If `account[r0]` does not exist, 0u64 is used.
    get.or_use account[r0] 0u64 into r2;
    // Increments `account[r0]` by `r1`.
    // If `r1 + r2` overflows, `transfer_private_to_public` is reverted.
    add r1 r2 into r3;
    // Updates the balance of the sender.
    set r3 into account[r0];

/**********************************************************************************************************************/

// The `transfer_public_to_private` function turns a specified amount
// from the mapping `account` into a record for the specified receiver.
//
// This function publicly reveals the sender, the receiver, and the specified amount.
// However, subsequent methods using the receiver's record can preserve the receiver's privacy.
function transfer_public_to_private:
    // Input the receiver.
    input r0 as address.private;
    // Input the amount.
    input r1 as u64.public;
    // Construct a record for the receiver.
    cast r0 r1 into r2 as credits.record;
    // Decrement the balance of the sender publicly.
    async transfer_public_to_private self.caller r1 into r3;
    // Output the record of the receiver.
    output r2 as credits.record;
    // Output the finalize future.
    output r3 as credits.aleo/transfer_public_to_private.future;

finalize transfer_public_to_private:
    // Input the sender.
    input r0 as address.public;
    // Input the amount.
    input r1 as u64.public;
    // Retrieve the balance of the sender.
    get account[r0] into r2;
    // Decrements `account[r0]` by `r1`.
    // If `r2 - r1` underflows, `transfer_public_to_private` is reverted.
    sub r2 r1 into r3;
    // Updates the balance of the sender.
    set r3 into account[r0];

/**********************************************************************************************************************/

// The `join` function combines two records into one.
function join:
    // Input the first record.
    input r0 as credits.record;
    // Input the second record.
    input r1 as credits.record;
    // Combines the amount of the first record and the second record.
    // This `add` operation is safe, and the proof will fail
    // if an overflow occurs.
    add r0.microcredits r1.microcredits into r2;
    // Construct a record with the combined amount.
    cast r0.owner r2 into r3 as credits.record;
    // Output the record.
    output r3 as credits.record;

/**********************************************************************************************************************/

// The `split` function splits a record into two records. The given input amount will be stored in the first record,
// and the remaining amount will be stored in the second record, with the fee deducted from the remaining amount.
// If the caller executes a transaction that contains only a call to this function, then the transaction does not
// require a fee, unless the caller wishes to provide an additional fee. Transactions that contain multiple transitions
// (that include one or more calls to this function) will require a fee as per standard consensus rules.
function split:
    // Input the record.
    input r0 as credits.record;
    // Input the amount to split.
    input r1 as u64.private;
    // Checks the given record has a sufficient amount to split.
    // This `sub` operation is safe, and the proof will fail
    // if an underflow occurs.
    sub r0.microcredits r1 into r2;
    // Checks the given record has a sufficient fee to remove.
    // This `sub` operation is safe, and the proof will fail
    // if an underflow occurs.
    sub r2 10_000u64 into r3;
    // Construct the first record.
    cast r0.owner r1 into r4 as credits.record;
    // Construct the second record.
    cast r0.owner r3 into r5 as credits.record;
    // Output the first record.
    output r4 as credits.record;
    // Output the second record.
    output r5 as credits.record;

/**********************************************************************************************************************/

// The `fee_private` function charges the specified amount from the sender's record.
function fee_private:
    // Input the sender's record.
    input r0 as credits.record;
    // Input the amount.
    input r1 as u64.public;
    // Input the priority fee amount.
    input r2 as u64.public;
    // Input the deployment or execution ID.
    input r3 as field.public;
    // Ensure the amount is nonzero.
    assert.neq r1 0u64;
    // Ensure the deployment or execution ID is nonzero.
    assert.neq r3 0field;
    // Add the fee and priority fee amounts.
    add r1 r2 into r4;
    // Checks the given record has a sufficient amount.
    // This `sub` operation is safe, and the proof will fail
    // if an underflow occurs. The destination register `r3` holds
    // the change amount for the sender.
    sub r0.microcredits r4 into r5;
    // Construct a record with the change amount for the sender.
    cast r0.owner r5 into r6 as credits.record;
    // Output the sender's change record.
    output r6 as credits.record;

/**********************************************************************************************************************/

// The `fee_public` function charges the specified amount from the sender's account.
function fee_public:
    // Input the amount.
    input r0 as u64.public;
    // Input the priority fee amount.
    input r1 as u64.public;
    // Input the deployment or execution ID.
    input r2 as field.public;
    // Ensure the amount is nonzero.
    assert.neq r0 0u64;
    // Ensure the deployment or execution ID is nonzero.
    assert.neq r2 0field;
    // Add the fee and priority fee amounts.
    add r0 r1 into r3;
    // Decrement the balance of the sender publicly.
    async fee_public self.signer r3 into r4;
    // Output the finalize future.
    output r4 as credits.aleo/fee_public.future;

finalize fee_public:
    // Input the sender's address.
    input r0 as address.public;
    // Input the total fee amount.
    input r1 as u64.public;
    // Retrieve the balance of the sender.
    // If `account[r0]` does not exist, `fee_public` is reverted.
    get account[r0] into r2;
    // Decrements `account[r0]` by `r1`.
    // If `r2 - r1` underflows, `fee_public` is reverted.
    sub r2 r1 into r3;
    // Updates the balance of the sender.
    set r3 into account[r0];

/**********************************************************************************************************************/

// Open Questions:
// fn bond
// - if the bond is now 33% or more, close the validator. (determine how hard to impl this)

/**********************************************************************************************************************/
