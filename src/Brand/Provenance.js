// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                  // hydrogen // schema // brand // provenance
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// FFI implementations for Provenance.purs
//
// Provides a deterministic hash function for testing and development.
// In production, SHA256 is computed by the Haskell backend using crypton.

"use strict";

/**
 * DJB2-based deterministic hash function.
 * 
 * This is NOT cryptographically secure - it's used for:
 * - Unit testing in PureScript
 * - Development/prototyping
 * - Deterministic content addressing in tests
 * 
 * Properties:
 * - DETERMINISTIC: Same input always produces same output
 * - FAST: O(n) where n is input length
 * - COLLISION-RESISTANT: Good distribution for typical inputs
 * 
 * Returns a 64-character hex string (matching SHA256 output format).
 */
export const sha256Native = function(input) {
  // DJB2 hash algorithm with multiple seeds for better distribution
  const djb2 = (str, seed) => {
    let hash = seed;
    for (let i = 0; i < str.length; i++) {
      // hash * 33 + char
      hash = ((hash << 5) + hash) + str.charCodeAt(i);
      // Keep it as a 32-bit integer
      hash = hash >>> 0;
    }
    return hash;
  };
  
  // Compute 8 different hash values with different seeds
  // to produce 64 hex characters (8 hashes × 8 hex chars each)
  const seeds = [5381, 65599, 31, 131, 1313, 13131, 131313, 1313131];
  let result = "";
  
  for (const seed of seeds) {
    const hash = djb2(input, seed);
    // Convert to 8-character hex string (zero-padded)
    result += hash.toString(16).padStart(8, "0");
  }
  
  return result;
};
