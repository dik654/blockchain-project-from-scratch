// Step 10: R1CS 가젯 — Poseidon 해시와 Merkle 증명을 회로로 표현
//
// "native 코드 = 회로 코드" 검증:
//   poseidon_hash(a, b) [native] == PoseidonChipset::hash(cs, a, b) [circuit]
//   verify_merkle_proof(...) [native] == MerkleProofCircuit::synthesize(cs) [circuit]
//
// 가젯(Gadget) = 반복적으로 사용되는 R1CS 패턴
//   Boolean, Mux(조건부 선택), S-box, MDS, Poseidon, Merkle

pub mod poseidon;
pub mod merkle;
