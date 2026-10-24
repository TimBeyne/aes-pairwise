import PairwiseIndependence.AES.ReferenceBridge

/-!
# Published AES test vectors proved in Lean

Ciphertext theorems use hexadecimal byte strings directly in their statements.
Finite computations use `native_decide`; decryption vectors follow from these
identities and the all-key symbolic inverse theorem.

Sources:
* FIPS 197 (2001), Appendices C.1–C.3 (canonical vectors and round starts):
  https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197.pdf
* FIPS 197 (2023), Appendices A.1–A.3 (complete expanded keys) and B:
  https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf
* NIST AES worked examples, ECB-AES128/192/256, encryption and decryption:
  https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/AES_Core_All.pdf

The reference implementation is related to the paper's fourth-SubBytes
checkpoint by the final theorem. These tests validate the implementation;
they do not transfer the independent-round-key probability bound to scheduled AES.
-/

namespace PairwiseIndependence

/-- FIPS 197 (2001), Appendix C.1: AES-128 encryption. -/
theorem aesReference_fips197_C1_encrypt :
    aesReferenceEncrypt .aes128
      (aesReferenceKeyOfHex .aes128 0x000102030405060708090a0b0c0d0e0f)
      (aesReferenceBlockOfHex 0x00112233445566778899aabbccddeeff) =
    aesReferenceBlockOfHex 0x69c4e0d86a7b0430d8cdb78070b4c55a := by
  native_decide

/-- The corresponding published inverse-cipher vector. -/
theorem aesReference_fips197_C1_decrypt :
    aesReferenceDecrypt .aes128
      (aesReferenceKeyOfHex .aes128 0x000102030405060708090a0b0c0d0e0f)
      (aesReferenceBlockOfHex 0x69c4e0d86a7b0430d8cdb78070b4c55a) =
    aesReferenceBlockOfHex 0x00112233445566778899aabbccddeeff := by
  rw [← aesReference_fips197_C1_encrypt]
  exact aesReferenceDecrypt_encrypt _ _ _

/-- FIPS 197 (2001), Appendix C.2: AES-192 encryption. -/
theorem aesReference_fips197_C2_encrypt :
    aesReferenceEncrypt .aes192
      (aesReferenceKeyOfHex .aes192 0x000102030405060708090a0b0c0d0e0f1011121314151617)
      (aesReferenceBlockOfHex 0x00112233445566778899aabbccddeeff) =
    aesReferenceBlockOfHex 0xdda97ca4864cdfe06eaf70a0ec0d7191 := by
  native_decide

/-- The corresponding published inverse-cipher vector. -/
theorem aesReference_fips197_C2_decrypt :
    aesReferenceDecrypt .aes192
      (aesReferenceKeyOfHex .aes192 0x000102030405060708090a0b0c0d0e0f1011121314151617)
      (aesReferenceBlockOfHex 0xdda97ca4864cdfe06eaf70a0ec0d7191) =
    aesReferenceBlockOfHex 0x00112233445566778899aabbccddeeff := by
  rw [← aesReference_fips197_C2_encrypt]
  exact aesReferenceDecrypt_encrypt _ _ _

/-- FIPS 197 (2001), Appendix C.3: AES-256 encryption. -/
theorem aesReference_fips197_C3_encrypt :
    aesReferenceEncrypt .aes256
      (aesReferenceKeyOfHex .aes256 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f)
      (aesReferenceBlockOfHex 0x00112233445566778899aabbccddeeff) =
    aesReferenceBlockOfHex 0x8ea2b7ca516745bfeafc49904b496089 := by
  native_decide

/-- The corresponding published inverse-cipher vector. -/
theorem aesReference_fips197_C3_decrypt :
    aesReferenceDecrypt .aes256
      (aesReferenceKeyOfHex .aes256 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f)
      (aesReferenceBlockOfHex 0x8ea2b7ca516745bfeafc49904b496089) =
    aesReferenceBlockOfHex 0x00112233445566778899aabbccddeeff := by
  rw [← aesReference_fips197_C3_encrypt]
  exact aesReferenceDecrypt_encrypt _ _ _

/-- FIPS 197 (2023), Appendix B's worked AES-128 cipher example. -/
theorem aesReference_fips197_B_encrypt :
    aesReferenceEncrypt .aes128
      (aesReferenceKeyOfHex .aes128 0x2b7e151628aed2a6abf7158809cf4f3c)
      (aesReferenceBlockOfHex 0x3243f6a8885a308d313198a2e0370734) =
    aesReferenceBlockOfHex 0x3925841d02dc09fbdc118597196a0b32 := by
  native_decide

theorem aesReference_fips197_B_decrypt :
    aesReferenceDecrypt .aes128
      (aesReferenceKeyOfHex .aes128 0x2b7e151628aed2a6abf7158809cf4f3c)
      (aesReferenceBlockOfHex 0x3925841d02dc09fbdc118597196a0b32) =
    aesReferenceBlockOfHex 0x3243f6a8885a308d313198a2e0370734 := by
  rw [← aesReference_fips197_B_encrypt]
  exact aesReferenceDecrypt_encrypt _ _ _

/-- NIST's four published ECB-AES128 encryption blocks. -/
theorem aesReference_nist_ecb128_encrypt :
    ([0x6bc1bee22e409f96e93d7e117393172a,
      0xae2d8a571e03ac9c9eb76fac45af8e51,
      0x30c81c46a35ce411e5fbc1191a0a52ef,
      0xf69f2445df4f9b17ad2b417be66c3710].map aesReferenceBlockOfHex).map
      (aesReferenceEncrypt .aes128 (aesReferenceKeyOfHex .aes128 0x2b7e151628aed2a6abf7158809cf4f3c)) =
    [0x3ad77bb40d7a3660a89ecaf32466ef97,
      0xf5d3d58503b9699de785895a96fdbaaf,
      0x43b1cd7f598ece23881b00e3ed030688,
      0x7b0c785e27e8ad3f8223207104725dd4].map aesReferenceBlockOfHex := by
  native_decide

/-- NIST's corresponding four ECB-AES128 decryption blocks. -/
theorem aesReference_nist_ecb128_decrypt :
    ([0x3ad77bb40d7a3660a89ecaf32466ef97,
      0xf5d3d58503b9699de785895a96fdbaaf,
      0x43b1cd7f598ece23881b00e3ed030688,
      0x7b0c785e27e8ad3f8223207104725dd4].map aesReferenceBlockOfHex).map
      (aesReferenceDecrypt .aes128 (aesReferenceKeyOfHex .aes128 0x2b7e151628aed2a6abf7158809cf4f3c)) =
    [0x6bc1bee22e409f96e93d7e117393172a,
      0xae2d8a571e03ac9c9eb76fac45af8e51,
      0x30c81c46a35ce411e5fbc1191a0a52ef,
      0xf69f2445df4f9b17ad2b417be66c3710].map aesReferenceBlockOfHex := by
  rw [← aesReference_nist_ecb128_encrypt]
  simp only [List.map_map, Function.comp_def, aesReferenceDecrypt_encrypt]

/-- FIPS 197 (2023), Appendix A.1: all 44 expanded AES-128 words. -/
theorem aesReference_fips197_A1_expandedKey :
    (aesReferenceExpandedKey .aes128
      (aesReferenceKeyOfHex .aes128 0x2b7e151628aed2a6abf7158809cf4f3c)).toList.map aesReferenceWordValue =
    [0x2b7e1516, 0x28aed2a6, 0xabf71588, 0x09cf4f3c,
      0xa0fafe17, 0x88542cb1, 0x23a33939, 0x2a6c7605,
      0xf2c295f2, 0x7a96b943, 0x5935807a, 0x7359f67f,
      0x3d80477d, 0x4716fe3e, 0x1e237e44, 0x6d7a883b,
      0xef44a541, 0xa8525b7f, 0xb671253b, 0xdb0bad00,
      0xd4d1c6f8, 0x7c839d87, 0xcaf2b8bc, 0x11f915bc,
      0x6d88a37a, 0x110b3efd, 0xdbf98641, 0xca0093fd,
      0x4e54f70e, 0x5f5fc9f3, 0x84a64fb2, 0x4ea6dc4f,
      0xead27321, 0xb58dbad2, 0x312bf560, 0x7f8d292f,
      0xac7766f3, 0x19fadc21, 0x28d12941, 0x575c006e,
      0xd014f9a8, 0xc9ee2589, 0xe13f0cc8, 0xb6630ca6] := by
  native_decide

/-- FIPS 197 (2001), Appendix C.1: the initial AddRoundKey state and
all 9 subsequent full-round boundary states, in the printed order. -/
theorem aesReference_fips197_C1_roundStarts :
    let w := aesReferenceExpandedKey .aes128
      (aesReferenceKeyOfHex .aes128 0x000102030405060708090a0b0c0d0e0f)
    let initial := aesReferenceAddRoundKey (aesReferenceBlockOfHex 0x00112233445566778899aabbccddeeff)
      (aesReferenceRoundKey w 0)
    (List.range 10).map (fun n => aesReferenceFullRounds w n initial) =
    [0x00102030405060708090a0b0c0d0e0f0,
      0x89d810e8855ace682d1843d8cb128fe4,
      0x4915598f55e5d7a0daca94fa1f0a63f7,
      0xfa636a2825b339c940668a3157244d17,
      0x247240236966b3fa6ed2753288425b6c,
      0xc81677bc9b7ac93b25027992b0261996,
      0xc62fe109f75eedc3cc79395d84f9cf5d,
      0xd1876c0f79c4300ab45594add66ff41f,
      0xfde3bad205e5d0d73547964ef1fe37f1,
      0xbd6e7c3df2b5779e0b61216e8b10b689].map aesReferenceBlockOfHex := by
  native_decide

/-- Appendix C.1's fourth SubBytes is the paper's four-round core checkpoint. -/
theorem aesReference_fips197_C1_fourthSubBytes :
    aesReferenceScheduledPaperCore .aes128
      (aesReferenceKeyOfHex .aes128 0x000102030405060708090a0b0c0d0e0f)
      (aesReferenceBlockOfHex 0x00112233445566778899aabbccddeeff) =
    aesReferenceBlockOfHex 0x2dfb02343f6d12dd09337ec75b36e3f0 := by
  native_decide

/-- NIST's four published ECB-AES192 encryption blocks. -/
theorem aesReference_nist_ecb192_encrypt :
    ([0x6bc1bee22e409f96e93d7e117393172a,
      0xae2d8a571e03ac9c9eb76fac45af8e51,
      0x30c81c46a35ce411e5fbc1191a0a52ef,
      0xf69f2445df4f9b17ad2b417be66c3710].map aesReferenceBlockOfHex).map
      (aesReferenceEncrypt .aes192 (aesReferenceKeyOfHex .aes192 0x8e73b0f7da0e6452c810f32b809079e562f8ead2522c6b7b)) =
    [0xbd334f1d6e45f25ff712a214571fa5cc,
      0x974104846d0ad3ad7734ecb3ecee4eef,
      0xef7afd2270e2e60adce0ba2face6444e,
      0x9a4b41ba738d6c72fb16691603c18e0e].map aesReferenceBlockOfHex := by
  native_decide

/-- NIST's corresponding four ECB-AES192 decryption blocks. -/
theorem aesReference_nist_ecb192_decrypt :
    ([0xbd334f1d6e45f25ff712a214571fa5cc,
      0x974104846d0ad3ad7734ecb3ecee4eef,
      0xef7afd2270e2e60adce0ba2face6444e,
      0x9a4b41ba738d6c72fb16691603c18e0e].map aesReferenceBlockOfHex).map
      (aesReferenceDecrypt .aes192 (aesReferenceKeyOfHex .aes192 0x8e73b0f7da0e6452c810f32b809079e562f8ead2522c6b7b)) =
    [0x6bc1bee22e409f96e93d7e117393172a,
      0xae2d8a571e03ac9c9eb76fac45af8e51,
      0x30c81c46a35ce411e5fbc1191a0a52ef,
      0xf69f2445df4f9b17ad2b417be66c3710].map aesReferenceBlockOfHex := by
  rw [← aesReference_nist_ecb192_encrypt]
  simp only [List.map_map, Function.comp_def, aesReferenceDecrypt_encrypt]

/-- FIPS 197 (2023), Appendix A.2: all 52 expanded AES-192 words. -/
theorem aesReference_fips197_A2_expandedKey :
    (aesReferenceExpandedKey .aes192
      (aesReferenceKeyOfHex .aes192 0x8e73b0f7da0e6452c810f32b809079e562f8ead2522c6b7b)).toList.map aesReferenceWordValue =
    [0x8e73b0f7, 0xda0e6452, 0xc810f32b, 0x809079e5,
      0x62f8ead2, 0x522c6b7b, 0xfe0c91f7, 0x2402f5a5,
      0xec12068e, 0x6c827f6b, 0x0e7a95b9, 0x5c56fec2,
      0x4db7b4bd, 0x69b54118, 0x85a74796, 0xe92538fd,
      0xe75fad44, 0xbb095386, 0x485af057, 0x21efb14f,
      0xa448f6d9, 0x4d6dce24, 0xaa326360, 0x113b30e6,
      0xa25e7ed5, 0x83b1cf9a, 0x27f93943, 0x6a94f767,
      0xc0a69407, 0xd19da4e1, 0xec1786eb, 0x6fa64971,
      0x485f7032, 0x22cb8755, 0xe26d1352, 0x33f0b7b3,
      0x40beeb28, 0x2f18a259, 0x6747d26b, 0x458c553e,
      0xa7e1466c, 0x9411f1df, 0x821f750a, 0xad07d753,
      0xca400538, 0x8fcc5006, 0x282d166a, 0xbc3ce7b5,
      0xe98ba06f, 0x448c773c, 0x8ecc7204, 0x01002202] := by
  native_decide

/-- FIPS 197 (2001), Appendix C.2: the initial AddRoundKey state and
all 11 subsequent full-round boundary states, in the printed order. -/
theorem aesReference_fips197_C2_roundStarts :
    let w := aesReferenceExpandedKey .aes192
      (aesReferenceKeyOfHex .aes192 0x000102030405060708090a0b0c0d0e0f1011121314151617)
    let initial := aesReferenceAddRoundKey (aesReferenceBlockOfHex 0x00112233445566778899aabbccddeeff)
      (aesReferenceRoundKey w 0)
    (List.range 12).map (fun n => aesReferenceFullRounds w n initial) =
    [0x00102030405060708090a0b0c0d0e0f0,
      0x4f63760643e0aa85aff8c9d041fa0de4,
      0xcb02818c17d2af9c62aa64428bb25fd7,
      0xf75c7778a327c8ed8cfebfc1a6c37f53,
      0x22ffc916a81474416496f19c64ae2532,
      0x80121e0776fd1d8a8d8c31bc965d1fee,
      0x671ef1fd4e2a1e03dfdcb1ef3d789b30,
      0x0c0370d00c01e622166b8accd6db3a2c,
      0x7255dad30fb80310e00d6c6b40d0527c,
      0xa906b254968af4e9b4bdb2d2f0c44336,
      0x88ec930ef5e7e4b6cc32f4c906d29414,
      0xafb73eeb1cd1b85162280f27fb20d585].map aesReferenceBlockOfHex := by
  native_decide

/-- Appendix C.2's fourth SubBytes is the paper's four-round core checkpoint. -/
theorem aesReference_fips197_C2_fourthSubBytes :
    aesReferenceScheduledPaperCore .aes192
      (aesReferenceKeyOfHex .aes192 0x000102030405060708090a0b0c0d0e0f1011121314151617)
      (aesReferenceBlockOfHex 0x00112233445566778899aabbccddeeff) =
    aesReferenceBlockOfHex 0x684af5bc0acce85564bb0878242ed2ed := by
  native_decide

/-- NIST's four published ECB-AES256 encryption blocks. -/
theorem aesReference_nist_ecb256_encrypt :
    ([0x6bc1bee22e409f96e93d7e117393172a,
      0xae2d8a571e03ac9c9eb76fac45af8e51,
      0x30c81c46a35ce411e5fbc1191a0a52ef,
      0xf69f2445df4f9b17ad2b417be66c3710].map aesReferenceBlockOfHex).map
      (aesReferenceEncrypt .aes256 (aesReferenceKeyOfHex .aes256 0x603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4)) =
    [0xf3eed1bdb5d2a03c064b5a7e3db181f8,
      0x591ccb10d410ed26dc5ba74a31362870,
      0xb6ed21b99ca6f4f9f153e7b1beafed1d,
      0x23304b7a39f9f3ff067d8d8f9e24ecc7].map aesReferenceBlockOfHex := by
  native_decide

/-- NIST's corresponding four ECB-AES256 decryption blocks. -/
theorem aesReference_nist_ecb256_decrypt :
    ([0xf3eed1bdb5d2a03c064b5a7e3db181f8,
      0x591ccb10d410ed26dc5ba74a31362870,
      0xb6ed21b99ca6f4f9f153e7b1beafed1d,
      0x23304b7a39f9f3ff067d8d8f9e24ecc7].map aesReferenceBlockOfHex).map
      (aesReferenceDecrypt .aes256 (aesReferenceKeyOfHex .aes256 0x603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4)) =
    [0x6bc1bee22e409f96e93d7e117393172a,
      0xae2d8a571e03ac9c9eb76fac45af8e51,
      0x30c81c46a35ce411e5fbc1191a0a52ef,
      0xf69f2445df4f9b17ad2b417be66c3710].map aesReferenceBlockOfHex := by
  rw [← aesReference_nist_ecb256_encrypt]
  simp only [List.map_map, Function.comp_def, aesReferenceDecrypt_encrypt]

/-- FIPS 197 (2023), Appendix A.3: all 60 expanded AES-256 words. -/
theorem aesReference_fips197_A3_expandedKey :
    (aesReferenceExpandedKey .aes256
      (aesReferenceKeyOfHex .aes256 0x603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4)).toList.map aesReferenceWordValue =
    [0x603deb10, 0x15ca71be, 0x2b73aef0, 0x857d7781,
      0x1f352c07, 0x3b6108d7, 0x2d9810a3, 0x0914dff4,
      0x9ba35411, 0x8e6925af, 0xa51a8b5f, 0x2067fcde,
      0xa8b09c1a, 0x93d194cd, 0xbe49846e, 0xb75d5b9a,
      0xd59aecb8, 0x5bf3c917, 0xfee94248, 0xde8ebe96,
      0xb5a9328a, 0x2678a647, 0x98312229, 0x2f6c79b3,
      0x812c81ad, 0xdadf48ba, 0x24360af2, 0xfab8b464,
      0x98c5bfc9, 0xbebd198e, 0x268c3ba7, 0x09e04214,
      0x68007bac, 0xb2df3316, 0x96e939e4, 0x6c518d80,
      0xc814e204, 0x76a9fb8a, 0x5025c02d, 0x59c58239,
      0xde136967, 0x6ccc5a71, 0xfa256395, 0x9674ee15,
      0x5886ca5d, 0x2e2f31d7, 0x7e0af1fa, 0x27cf73c3,
      0x749c47ab, 0x18501dda, 0xe2757e4f, 0x7401905a,
      0xcafaaae3, 0xe4d59b34, 0x9adf6ace, 0xbd10190d,
      0xfe4890d1, 0xe6188d0b, 0x046df344, 0x706c631e] := by
  native_decide

/-- FIPS 197 (2001), Appendix C.3: the initial AddRoundKey state and
all 13 subsequent full-round boundary states, in the printed order. -/
theorem aesReference_fips197_C3_roundStarts :
    let w := aesReferenceExpandedKey .aes256
      (aesReferenceKeyOfHex .aes256 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f)
    let initial := aesReferenceAddRoundKey (aesReferenceBlockOfHex 0x00112233445566778899aabbccddeeff)
      (aesReferenceRoundKey w 0)
    (List.range 14).map (fun n => aesReferenceFullRounds w n initial) =
    [0x00102030405060708090a0b0c0d0e0f0,
      0x4f63760643e0aa85efa7213201a4e705,
      0x1859fbc28a1c00a078ed8aadc42f6109,
      0x975c66c1cb9f3fa8a93a28df8ee10f63,
      0x1c05f271a417e04ff921c5c104701554,
      0xc357aae11b45b7b0a2c7bd28a8dc99fa,
      0x7f074143cb4e243ec10c815d8375d54c,
      0xd653a4696ca0bc0f5acaab5db96c5e7d,
      0x5aa858395fd28d7d05e1a38868f3b9c5,
      0x4a824851c57e7e47643de50c2af3e8c9,
      0xc14907f6ca3b3aa070e9aa313b52b5ec,
      0x5f9c6abfbac634aa50409fa766677653,
      0x516604954353950314fb86e401922521,
      0x627bceb9999d5aaac945ecf423f56da5].map aesReferenceBlockOfHex := by
  native_decide

/-- Appendix C.3's fourth SubBytes is the paper's four-round core checkpoint. -/
theorem aesReference_fips197_C3_fourthSubBytes :
    aesReferenceScheduledPaperCore .aes256
      (aesReferenceKeyOfHex .aes256 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f)
      (aesReferenceBlockOfHex 0x00112233445566778899aabbccddeeff) =
    aesReferenceBlockOfHex 0x884a33781fdb75c2d380349e19f876fb := by
  native_decide

/-- The map used in Theorem 5, instantiated with FIPS C.1 scheduled keys
and initial state, agrees with the published fourth-SubBytes state. -/
theorem aesIndependentFourRoundCore_fips197_C1 :
    let w := aesReferenceExpandedKey .aes128
      (aesReferenceKeyOfHex .aes128 0x000102030405060708090a0b0c0d0e0f)
    aesIndependentFourRoundCore
      (aesReferenceDecode (aesReferenceRoundKey w 1),
       aesReferenceDecode (aesReferenceRoundKey w 2),
       aesReferenceDecode (aesReferenceRoundKey w 3))
      (aesReferenceDecode (aesReferenceBlockOfHex 0x00112233445566778899aabbccddeeff) +
       aesReferenceDecode (aesReferenceRoundKey w 0)) =
    aesReferenceDecode (aesReferenceBlockOfHex 0x2dfb02343f6d12dd09337ec75b36e3f0) := by
  dsimp only
  rw [← aesReferenceScheduledPaperCore_decode]
  rw [aesReference_fips197_C1_fourthSubBytes]

end PairwiseIndependence
