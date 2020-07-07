(*Two tactics to make use of quotation easier inside proofs*)
let (HOLE_ABSORB_TAC: tactic) = fun (asm,gl) -> PURE_REWRITE_TAC[HOLE_ABSORB_CONV gl] (asm,gl);; 
let (QUOTE_TO_CONSTRUCTION_TAC: tactic) = fun (asm,gl) -> PURE_REWRITE_TAC[QUOTE_TO_CONSTRUCTION_CONV gl] (asm,gl);;
