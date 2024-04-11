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

pub fn arc_38_program() -> &'static str {
  r"
  import credits.aleo;
  program arc_0038.aleo;
  
  // Constants
  // ADMIN: address = aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs - the admin address is the address of the contract creator
  // CORE_PROTOCOL: address = aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt - the address of this program
  // SHARES_TO_MICROCREDITS: u64 = 1_000u64;
  // PRECISION_UNSIGNED: u128 = 1_000u128;
  // MAX_COMMISSION_RATE: u128 = 500u128;
  // UNBONDING_PERIOD: u32 = 360u32;
  // MINIMUM_BOND_AMOUNT: u64 = 10_000_000_000u64;
  
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
      lt r0 1_000u128 into r2;
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
      mul r2 1_000u64 into r8;
      set r8 into total_shares[0u8];
      set r8 into delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs];
  
  
  
  
  function get_commission_test:
      input r0 as u128.private;
      input r1 as u128.private;
      mul r0 r1 into r2;
      div r2 1_000u128 into r3;
      cast r3 into r4 as u64;
      output r4 as u64.private;
  
  
  
  
  function calculate_new_shares_test:
      input r0 as u128.private;
      input r1 as u128.private;
      input r2 as u128.private;
      input r3 as u128.private;
      add r0 r1 into r4;
      mul r3 1_000u128 into r5;
      add r4 r2 into r6;
      mul r5 r6 into r7;
      mul r4 1_000u128 into r8;
      div r7 r8 into r9;
      sub r9 r3 into r10;
      cast r10 into r11 as u64;
      output r11 as u64.private;
  
  
  function set_commission_percent:
      input r0 as u128.public;
      assert.eq self.caller aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs;
      lt r0 1_000u128 into r1;
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
      cast r2.microcredits into r6 as i64;
      cast r3 into r7 as i64;
      sub r6 r7 into r8;
      ternary r5 r8 0i64 into r9;
      get commission_percent[0u8] into r10;
      cast r9 into r11 as u128;
      mul r11 r10 into r12;
      div r12 1_000u128 into r13;
      cast r13 into r14 as u64;
      cast r9 into r15 as u64;
      sub r15 r14 into r16;
      add r3 r16 into r17;
      get pending_deposits[0u8] into r18;
      cast r17 into r19 as u128;
      cast r18 into r20 as u128;
      cast r14 into r21 as u128;
      cast r4 into r22 as u128;
      add r19 r20 into r23;
      mul r22 1_000u128 into r24;
      add r23 r21 into r25;
      mul r24 r25 into r26;
      mul r23 1_000u128 into r27;
      div r26 r27 into r28;
      sub r28 r22 into r29;
      cast r29 into r30 as u64;
      get.or_use delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs] 0u64 into r31;
      add r31 r30 into r32;
      set r32 into delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs];
      add r4 r30 into r33;
      set r33 into total_shares[0u8];
      add r17 r14 into r34;
      set r34 into total_balance[0u8];
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
      cast r7 into r11 as i64;
      cast r8 into r12 as i64;
      sub r11 r12 into r13;
      ternary r10 r13 0i64 into r14;
      get commission_percent[0u8] into r15;
      cast r14 into r16 as u128;
      mul r16 r15 into r17;
      div r17 1_000u128 into r18;
      cast r18 into r19 as u64;
      cast r14 into r20 as u64;
      sub r20 r19 into r21;
      add r8 r21 into r22;
      get pending_deposits[0u8] into r23;
      cast r22 into r24 as u128;
      cast r23 into r25 as u128;
      cast r19 into r26 as u128;
      cast r9 into r27 as u128;
      add r24 r25 into r28;
      mul r27 1_000u128 into r29;
      add r28 r26 into r30;
      mul r29 r30 into r31;
      mul r28 1_000u128 into r32;
      div r31 r32 into r33;
      sub r33 r27 into r34;
      cast r34 into r35 as u64;
      get.or_use delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs] 0u64 into r36;
      add r36 r35 into r37;
      set r37 into delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs];
      add r9 r35 into r38;
      set r38 into total_shares[0u8];
      add r22 r19 into r39;
      set r39 into total_balance[0u8];
  
  
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
      async bond_deposits r2 r1 r0 into r3;
      output r3 as arc_0038.aleo/bond_deposits.future;
  
  finalize bond_deposits:
      input r0 as credits.aleo/bond_public.future;
      input r1 as u64.public;
      input r2 as address.public;
      await r0;
      get.or_use credits.aleo/account[aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt] 0u64 into r3;
      get pending_withdrawal[1u8] into r4;
      gte r3 r4 into r5;
      assert.eq r5 true;
      get total_balance[0u8] into r6;
      get pending_deposits[0u8] into r7;
      sub r7 r1 into r8;
      set r8 into pending_deposits[0u8];
      add r6 r1 into r9;
      set r9 into total_balance[0u8];
      contains validator[1u8] into r10;
      assert.eq r10 false;
      get validator[0u8] into r11;
      assert.eq r11 r2;
  
  
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
      cast r1.microcredits into r5 as i64;
      cast r2 into r6 as i64;
      sub r5 r6 into r7;
      ternary r4 r7 0i64 into r8;
      get commission_percent[0u8] into r9;
      cast r8 into r10 as u128;
      mul r10 r9 into r11;
      div r11 1_000u128 into r12;
      cast r12 into r13 as u64;
      cast r8 into r14 as u64;
      sub r14 r13 into r15;
      add r2 r15 into r16;
      get pending_deposits[0u8] into r17;
      cast r16 into r18 as u128;
      cast r17 into r19 as u128;
      cast r13 into r20 as u128;
      cast r3 into r21 as u128;
      add r18 r19 into r22;
      mul r21 1_000u128 into r23;
      add r22 r20 into r24;
      mul r23 r24 into r25;
      mul r22 1_000u128 into r26;
      div r25 r26 into r27;
      sub r27 r21 into r28;
      cast r28 into r29 as u64;
      get.or_use delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs] 0u64 into r30;
      add r30 r29 into r31;
      set r31 into delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs];
      add r3 r29 into r32;
      set r32 into total_shares[0u8];
      add r16 r13 into r33;
      set r33 into total_balance[0u8];
  
  
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
      cast r4.microcredits into r8 as i64;
      cast r5 into r9 as i64;
      sub r8 r9 into r10;
      ternary r7 r10 0i64 into r11;
      get commission_percent[0u8] into r12;
      cast r11 into r13 as u128;
      mul r13 r12 into r14;
      div r14 1_000u128 into r15;
      cast r15 into r16 as u64;
      cast r11 into r17 as u64;
      sub r17 r16 into r18;
      add r5 r18 into r19;
      get pending_deposits[0u8] into r20;
      cast r19 into r21 as u128;
      cast r20 into r22 as u128;
      cast r16 into r23 as u128;
      cast r6 into r24 as u128;
      add r21 r22 into r25;
      mul r24 1_000u128 into r26;
      add r25 r23 into r27;
      mul r26 r27 into r28;
      mul r25 1_000u128 into r29;
      div r28 r29 into r30;
      sub r30 r24 into r31;
      cast r31 into r32 as u64;
      get.or_use delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs] 0u64 into r33;
      add r33 r32 into r34;
      set r34 into delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs];
      add r6 r32 into r35;
      add r19 r16 into r36;
  // Update total balance to include rewards
      set r36 into total_balance[0u8];
  // Calculate shares to mint for deposit
      cast r36 into r37 as u128;
      cast r20 into r38 as u128;
      cast r2 into r39 as u128;
      cast r35 into r40 as u128;
      add r37 r38 into r41;
      mul r40 1_000u128 into r42;
      add r41 r39 into r43;
      mul r42 r43 into r44;
      mul r41 1_000u128 into r45;
      div r44 r45 into r46;
      sub r46 r40 into r47;
      cast r47 into r48 as u64;
  // Make sure the deposit is not too small
      gte r48 1u64 into r49;
      assert.eq r49 true;
  // Update delegator shares
      get.or_use delegator_shares[r1] 0u64 into r50;
      add r50 r48 into r51;
      set r51 into delegator_shares[r1];
  // Update total shares
      add r35 r48 into r52;
      set r52 into total_shares[0u8];
  // Update pending deposits
      add r20 r2 into r53;
      set r53 into pending_deposits[0u8];
  
  
  
  
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
      gte r18 10_000_000_000u64 into r19;
      cast aleo1q6qstg8q8shwqf5m6q5fcenuwsdqsvp4hhsgfnx5chzjm3secyzqt9mxm8 0u64 into r20 as bond_state;
      get.or_use credits.aleo/bonded[aleo1j0zju7f0fpgv98gulyywtkxk6jca99l6425uqhnd5kccu4jc2grstjx0mt] r20 into r21;
      gte r21.microcredits 10_000_000_000u64 into r22;
  // Allow the withdrawal if the pool is still bonded, or if there are not enough deposits to maintain the minimum bond amount
      not r19 into r23;
      or r22 r23 into r24;
      assert.eq r24 true;
  // Add back the newly unbonded credits to appropriately calculate rewards before the withdrawal
      add r21.microcredits r15 into r25;
  // Distribute shares for new commission
      get total_balance[0u8] into r26;
      get total_shares[0u8] into r27;
      gt r25 r26 into r28;
      cast r25 into r29 as i64;
      cast r26 into r30 as i64;
      sub r29 r30 into r31;
      ternary r28 r31 0i64 into r32;
      get commission_percent[0u8] into r33;
      cast r32 into r34 as u128;
      mul r34 r33 into r35;
      div r35 1_000u128 into r36;
      cast r36 into r37 as u64;
      cast r32 into r38 as u64;
      sub r38 r37 into r39;
      add r26 r39 into r40;
      cast r40 into r41 as u128;
      cast r16 into r42 as u128;
      cast r37 into r43 as u128;
      cast r27 into r44 as u128;
      add r41 r42 into r45;
      mul r44 1_000u128 into r46;
      add r45 r43 into r47;
      mul r46 r47 into r48;
      mul r45 1_000u128 into r49;
      div r48 r49 into r50;
      sub r50 r44 into r51;
      cast r51 into r52 as u64;
      get.or_use delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs] 0u64 into r53;
      add r53 r52 into r54;
      set r54 into delegator_shares[aleo15055whvfcf6hnysnxu6czv7zmhxhrp69lhl2gdee4lyxgxkglv9sx943hs];
      add r27 r52 into r55;
      add r40 r37 into r56;
      cast r56 into r57 as u128;
      cast r16 into r58 as u128;
  // Calculate full pool size
      add r57 r58 into r59;
  // Calculate withdrawal amount
      cast r1 into r60 as u128;
      cast r59 into r61 as u128;
      mul r60 r61 into r62;
      mul r62 1_000u128 into r63;
      cast r55 into r64 as u128;
      mul r64 1_000u128 into r65;
      div r63 r65 into r66;
      cast r2 into r67 as u128;
  // If the calculated withdrawal amount is greater than total_withdrawal, the excess will stay in the pool
      gte r66 r67 into r68;
      assert.eq r68 true;
  // Update withdrawals mappings
      div block.height 1000u32 into r69;
      mul r69 1000u32 into r70;
      add r70 1000u32 into r71;
      ternary r7 r71 r5 into r72;
      set r72 into current_batch_height[0u8];
      cast r2 r72 into r73 as withdrawal_state;
      set r73 into withdrawals[r3];
  // Update pending withdrawal
      add r14 r2 into r74;
      set r74 into pending_withdrawal[0u8];
  // Update total balance
      sub r56 r2 into r75;
      set r75 into total_balance[0u8];
  // Update total shares
      sub r55 r1 into r76;
      set r76 into total_shares[0u8];
  // Update delegator_shares mapping
      get delegator_shares[r3] into r77;
      sub r77 r1 into r78;
      set r78 into delegator_shares[r3];
  
  
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
      mul r16 1_000u128 into r17;
      cast r14 into r18 as u128;
      mul r18 1_000u128 into r19;
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
  
  "
}