//! Argus is a minimal, blazing fast contract storage introspection tool written in rust.
//!
//! It is designed to extract storage mapping slots from a contract, without needing to know the
//! contract's source code.

use alloy::{
    network::TransactionBuilder,
    primitives::{address, bytes, Address, Bytes, U256},
    providers::{ext::TraceApi, ProviderBuilder},
    rpc::types::{trace::parity::TraceType, TransactionRequest},
};
use eyre::{bail, OptionExt, Result};
use std::{collections::VecDeque, fmt::Debug};

/// The `Introspector` struct is used to introspect a contract's storage and determine which
/// standards it adheres to.
#[derive(Debug, Clone)]
pub struct Introspector {
    /// The contract address to introspect.
    pub contract_address: Address,
    /// The provider to use for querying the contract. Supports WebSocket, IPC, and HTTP
    /// transports.
    rpc_url: String,
}

/// The `IntrospectResult` struct is used to store the results of an introspection.
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct IntrospectResult {
    /// The balance slot of the contract.
    pub balance_slot: Option<U256>,
    /// The allowance slot of the contract.
    pub allowance_slot: Option<U256>,
    /// The token approvals slot of the contract.
    pub token_approvals_slot: Option<U256>,
    /// The operator approvals slot of the contract.
    pub operator_approvals_slot: Option<U256>,
    /// The erc1155 balance slot of the contract.
    pub erc_1155_balance_slot: Option<U256>,
}

const INTROSPECT_ADDRESS: Address = address!("000000000000000000696c6f76656f7474657273");

impl Introspector {
    /// Creates a new `Introspector` instance with the given `contract_address` and `provider`.
    pub fn try_new(contract_address: Address, rpc_url: impl Into<String>) -> Self {
        Self { contract_address, rpc_url: rpc_url.into() }
    }

    /// Run an introspection on the contract and return the results.
    ///
    /// Performs the following calls, returning the base slot for each:
    /// - balanceOf(address)
    /// - allowance(address, address)
    /// - getApproved(address)
    /// - isApprovedForAll(address, address)
    /// - balanceOf(address, uint256)
    pub async fn run(&self) -> Result<IntrospectResult> {
        let balance_slot_future = self.get_balance_slot();
        let allowance_slot_future = self.get_allowance_slot();
        let token_approvals_slot_future = self.get_token_approvals_slot();
        let operator_approvals_slot_future = self.get_operator_approvals_slot();
        let erc_1155_balance_slot_future = self.get_erc_1155_balance_slot();

        // Run all calls concurrently.
        let (
            balance_slot_result,
            allowance_slot_result,
            token_approvals_slot_result,
            operator_approvals_slot_result,
            erc_1155_balance_slot_result,
        ) = futures::future::join5(
            balance_slot_future,
            allowance_slot_future,
            token_approvals_slot_future,
            operator_approvals_slot_future,
            erc_1155_balance_slot_future,
        )
        .await;

        let maybe_erc_20 = balance_slot_result.is_ok() && allowance_slot_result.is_ok();
        let maybe_erc_721 = balance_slot_result.is_ok() &&
            token_approvals_slot_result.is_ok() &&
            operator_approvals_slot_result.is_ok();
        let maybe_erc_1155 =
            operator_approvals_slot_result.is_ok() && erc_1155_balance_slot_result.is_ok();

        if maybe_erc_20 {
            Ok(IntrospectResult {
                balance_slot: balance_slot_result.ok(),
                allowance_slot: allowance_slot_result.ok(),
                ..Default::default()
            })
        } else if maybe_erc_721 {
            Ok(IntrospectResult {
                balance_slot: balance_slot_result.ok(),
                token_approvals_slot: token_approvals_slot_result.ok(),
                operator_approvals_slot: operator_approvals_slot_result.ok(),
                ..Default::default()
            })
        } else if maybe_erc_1155 {
            Ok(IntrospectResult {
                operator_approvals_slot: operator_approvals_slot_result.ok(),
                erc_1155_balance_slot: erc_1155_balance_slot_result.ok(),
                ..Default::default()
            })
        } else {
            Ok(IntrospectResult {
                balance_slot: balance_slot_result.ok(),
                allowance_slot: allowance_slot_result.ok(),
                token_approvals_slot: token_approvals_slot_result.ok(),
                operator_approvals_slot: operator_approvals_slot_result.ok(),
                erc_1155_balance_slot: erc_1155_balance_slot_result.ok(),
            })
        }
    }

    /// Get the balance slot of the contract by tracing a call to `balanceOf(address)`.
    pub async fn get_balance_slot(&self) -> Result<U256> {
        let calldata =
            bytes!("70a08231000000000000000000000000000000000000000000696c6f76656f7474657273"); // balanceOf(INTROSPECT_ADDRESS)
        return self.extract_slot(calldata).await;
    }

    /// Get the allowance slot of the contract by tracing a call to `allowance(address, address)`.
    pub async fn get_allowance_slot(&self) -> Result<U256> {
        let calldata =
            bytes!("dd62ed3e000000000000000000000000000000000000000000696c6f76656f7474657273000000000000000000000000000000000000000000696c6f76656f7474657273"); // allowance(INTROSPECT_ADDRESS, INTROSPECT_ADDRESS)
        return self.extract_slot(calldata).await;
    }

    /// Get the token approvals slot of the contract by tracing a call to `getApproved(address)`.
    pub async fn get_token_approvals_slot(&self) -> Result<U256> {
        let calldata =
            bytes!("081812fc000000000000000000000000000000000000000000696c6f76656f7474657273"); // getApproved(INTROSPECT_ADDRESS)
        return self.extract_slot(calldata).await;
    }

    /// Get the operator approvals slot of the contract by tracing a call to
    /// `isApprovedForAll(address, address)`.
    pub async fn get_operator_approvals_slot(&self) -> Result<U256> {
        let calldata =
            bytes!("e985e9c5000000000000000000000000000000000000000000696c6f76656f7474657273000000000000000000000000000000000000000000696c6f76656f7474657273"); // isApprovedForAll(INTROSPECT_ADDRESS, INTROSPECT_ADDRESS)
        return self.extract_slot(calldata).await;
    }

    /// Get the erc1155 balance slot of the contract by tracing a call to `balanceOf(address,
    /// uint256)`.
    pub async fn get_erc_1155_balance_slot(&self) -> Result<U256> {
        let calldata =
            bytes!("00fdd58e000000000000000000000000000000000000000000696c6f76656f7474657273000000000000000000000000000000000000000000696c6f76656f7474657273"); // balanceOf(INTROSPECT_ADDRESS, INTROSPECT_ADDRESS)
        return self.extract_slot(calldata).await;
    }

    /// Extract the slot from the given calldata.
    ///
    /// This function traces the call to the contract and extracts the slot
    /// from the trace by monitoring the stack and memory, and looking for sha3 operations.
    ///
    /// Mapping slots are stored in the format:
    /// `keccak256(bytes32(mapping_key) + bytes32(slot))`
    ///
    /// For example, the mapping slot for `balanceOf(0x000...123)` is stored as:
    /// `keccak256(0x00000000000000000000000000000000000000000000000000000000000001230000000000000000000000000000000000000000000000000000000000000001)`
    ///
    /// In this case, the mapping key (address) is `0x000...123` and the slot is `1`, so we return
    /// `1`.
    async fn extract_slot(&self, calldata: Bytes) -> Result<U256> {
        let provider = ProviderBuilder::new().on_builtin(&self.rpc_url).await?;

        let mut tx = TransactionRequest::default()
            .with_from(INTROSPECT_ADDRESS)
            .with_to(self.contract_address)
            .with_input(calldata.clone());
        tx.input.data = Some(calldata);

        let result = provider
            .trace_call(&tx, &[TraceType::VmTrace, TraceType::Trace])
            .await?
            .vm_trace
            .ok_or_eyre("vm trace not found")?
            .ops;

        // A naive stack impl. We don't track this accurately, but it's good enough for our
        // purposes.
        let mut stack: VecDeque<U256> = VecDeque::new();
        let mut memory: Vec<u8> = Vec::new();

        for instruction in result {
            if let Some(executed) = &instruction.ex {
                if let Some(memory_delta) = &executed.mem {
                    let offset = memory_delta.off;
                    let data = memory_delta.data.to_vec();

                    // expand memory if necessary
                    if memory.len() < offset + data.len() {
                        memory.resize(offset + data.len(), 0);
                    }

                    // copy data into memory at the given offset
                    memory[offset..offset + data.len()].copy_from_slice(&data);
                }

                stack.extend(executed.push.iter());
            }

            if let Some(opcode) = &instruction.op {
                // If we see a SHA3, we can extract the contents that are being hashed.
                // We store these contents in a
                if ["KECCAK256", "SHA3"].contains(&opcode.as_str()) {
                    let _ = stack.pop_back().ok_or_eyre("stack underflow")?; // pop off the hashed value
                    let offset: usize =
                        stack.pop_back().ok_or_eyre("stack underflow")?.try_into()?;
                    let size: usize = stack.pop_back().ok_or_eyre("stack underflow")?.try_into()?;

                    let data = memory[offset..offset + size].to_vec();

                    // is data of the format bytes32(INTROSPECT_ADDRESS).concat(bytes32(N))?
                    if data.len() == 64 && &data[12..32] == INTROSPECT_ADDRESS.as_slice() {
                        // get the second 32 bytes, converted to U256. this is the mapping slot.
                        let balance_slot: U256 = U256::from_be_slice(&data[32..64]);
                        return Ok(balance_slot);
                    }
                }
            }
        }

        bail!("failed to get balance slot")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy::primitives::address;

    #[tokio::test]
    async fn test_introspect_erc20() {
        let rpc_url = std::env::var("RPC_URL").unwrap_or_else(|_| {
            println!("RPC_URL not set, skipping test");
            std::process::exit(0);
        });

        let contract_address = address!("c02aaa39b223fe8d0a0e5c4f27ead9083c756cc2");
        let introspector = Introspector::try_new(contract_address, rpc_url);

        let res = introspector.run().await.expect("failed to run introspection");
        assert_eq!(
            res,
            IntrospectResult {
                balance_slot: Some(U256::from(3)),
                allowance_slot: Some(U256::from(4)),
                ..Default::default()
            }
        );
    }

    #[tokio::test]
    async fn test_introspect_erc721() {
        let rpc_url = std::env::var("RPC_URL").unwrap_or_else(|_| {
            println!("RPC_URL not set, skipping test");
            std::process::exit(0);
        });

        let contract_address = address!("bc4ca0eda7647a8ab7c2061c2e118a18a936f13d");
        let introspector = Introspector::try_new(contract_address, rpc_url);

        let res = introspector.run().await.expect("failed to run introspection");
        assert_eq!(
            res,
            IntrospectResult {
                balance_slot: Some(U256::from(1)),
                token_approvals_slot: Some(U256::from(3)),
                operator_approvals_slot: Some(U256::from(5)),
                ..Default::default()
            }
        );
    }

    #[tokio::test]
    async fn test_introspect_erc1155() {
        let rpc_url = std::env::var("RPC_URL").unwrap_or_else(|_| {
            println!("RPC_URL not set, skipping test");
            std::process::exit(0);
        });

        let contract_address = address!("c552292732f7a9a4a494da557b47bc01e01722df");
        let introspector = Introspector::try_new(contract_address, rpc_url);

        let res = introspector.run().await.expect("failed to run introspection");
        assert_eq!(
            res,
            IntrospectResult {
                operator_approvals_slot: Some(U256::from(1)),
                erc_1155_balance_slot: Some(U256::from(0)),
                ..Default::default()
            }
        );
    }
}
