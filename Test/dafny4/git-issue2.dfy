// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type sp_state
type operand = int

function sp_op_const(c:int) : int { c }

predicate {:opaque} InBounds(s:sp_state, o:operand, v:int)
{
    0 <= o < 0x1_0000_0000
}

lemma lemma_K_InBounds()
    ensures forall s:sp_state ::
                InBounds(s, sp_op_const(0x428a2f98), 0x428a2f98) &&
                InBounds(s, sp_op_const(0x71374491), 0x71374491) &&
                InBounds(s, sp_op_const(0xb5c0fbcf), 0xb5c0fbcf) &&
                InBounds(s, sp_op_const(0xe9b5dba5), 0xe9b5dba5) &&
                InBounds(s, sp_op_const(0x3956c25b), 0x3956c25b) &&
                InBounds(s, sp_op_const(0x59f111f1), 0x59f111f1) &&
                InBounds(s, sp_op_const(0x923f82a4), 0x923f82a4) &&
                InBounds(s, sp_op_const(0xab1c5ed5), 0xab1c5ed5) &&
                InBounds(s, sp_op_const(0xd807aa98), 0xd807aa98) &&
                InBounds(s, sp_op_const(0x12835b01), 0x12835b01) &&
                InBounds(s, sp_op_const(0x243185be), 0x243185be) &&
                InBounds(s, sp_op_const(0x550c7dc3), 0x550c7dc3) &&
                InBounds(s, sp_op_const(0x72be5d74), 0x72be5d74) &&
                InBounds(s, sp_op_const(0x80deb1fe), 0x80deb1fe) &&
                InBounds(s, sp_op_const(0x9bdc06a7), 0x9bdc06a7) &&
                InBounds(s, sp_op_const(0xc19bf174), 0xc19bf174) &&
                InBounds(s, sp_op_const(0xe49b69c1), 0xe49b69c1) &&
                InBounds(s, sp_op_const(0xefbe4786), 0xefbe4786) &&
                InBounds(s, sp_op_const(0x0fc19dc6), 0x0fc19dc6) &&
                InBounds(s, sp_op_const(0x240ca1cc), 0x240ca1cc) &&
                InBounds(s, sp_op_const(0x2de92c6f), 0x2de92c6f) &&
                InBounds(s, sp_op_const(0x4a7484aa), 0x4a7484aa) &&
                InBounds(s, sp_op_const(0x5cb0a9dc), 0x5cb0a9dc) &&
                InBounds(s, sp_op_const(0x76f988da), 0x76f988da) &&
                InBounds(s, sp_op_const(0x983e5152), 0x983e5152) &&
                InBounds(s, sp_op_const(0xa831c66d), 0xa831c66d) &&
                InBounds(s, sp_op_const(0xb00327c8), 0xb00327c8) &&
                InBounds(s, sp_op_const(0xbf597fc7), 0xbf597fc7) &&
                InBounds(s, sp_op_const(0xc6e00bf3), 0xc6e00bf3) &&
                InBounds(s, sp_op_const(0xd5a79147), 0xd5a79147) &&
                InBounds(s, sp_op_const(0x06ca6351), 0x06ca6351) &&
                InBounds(s, sp_op_const(0x14292967), 0x14292967) &&
                InBounds(s, sp_op_const(0x27b70a85), 0x27b70a85) &&
                InBounds(s, sp_op_const(0x2e1b2138), 0x2e1b2138) &&
                InBounds(s, sp_op_const(0x4d2c6dfc), 0x4d2c6dfc) &&
                InBounds(s, sp_op_const(0x53380d13), 0x53380d13) &&
                InBounds(s, sp_op_const(0x650a7354), 0x650a7354) &&
                InBounds(s, sp_op_const(0x766a0abb), 0x766a0abb) &&
                InBounds(s, sp_op_const(0x81c2c92e), 0x81c2c92e) &&
                InBounds(s, sp_op_const(0x92722c85), 0x92722c85) &&
                InBounds(s, sp_op_const(0xa2bfe8a1), 0xa2bfe8a1) &&
                InBounds(s, sp_op_const(0xa81a664b), 0xa81a664b) &&
                InBounds(s, sp_op_const(0xc24b8b70), 0xc24b8b70) &&
                InBounds(s, sp_op_const(0xc76c51a3), 0xc76c51a3) &&
                InBounds(s, sp_op_const(0xd192e819), 0xd192e819) &&
                InBounds(s, sp_op_const(0xd6990624), 0xd6990624) &&
                InBounds(s, sp_op_const(0xf40e3585), 0xf40e3585) &&
                InBounds(s, sp_op_const(0x106aa070), 0x106aa070) &&
                InBounds(s, sp_op_const(0x19a4c116), 0x19a4c116) &&
                InBounds(s, sp_op_const(0x1e376c08), 0x1e376c08) &&
                InBounds(s, sp_op_const(0x2748774c), 0x2748774c) &&
                InBounds(s, sp_op_const(0x34b0bcb5), 0x34b0bcb5) &&
                InBounds(s, sp_op_const(0x391c0cb3), 0x391c0cb3) &&
                InBounds(s, sp_op_const(0x4ed8aa4a), 0x4ed8aa4a) &&
                InBounds(s, sp_op_const(0x5b9cca4f), 0x5b9cca4f) &&
                InBounds(s, sp_op_const(0x682e6ff3), 0x682e6ff3) &&
                InBounds(s, sp_op_const(0x748f82ee), 0x748f82ee) &&
                InBounds(s, sp_op_const(0x78a5636f), 0x78a5636f) &&
                InBounds(s, sp_op_const(0x84c87814), 0x84c87814) &&
                InBounds(s, sp_op_const(0x8cc70208), 0x8cc70208) &&
                InBounds(s, sp_op_const(0x90befffa), 0x90befffa) &&
                InBounds(s, sp_op_const(0xa4506ceb), 0xa4506ceb) &&
                InBounds(s, sp_op_const(0xbef9a3f7), 0xbef9a3f7) &&
                InBounds(s, sp_op_const(0xc67178f2), 0xc67178f2)
{ reveal_InBounds(); }



