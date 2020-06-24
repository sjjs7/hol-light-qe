(*Two tactics to make use of quotation easier inside proofs*)
let (UNQUOTE_TAC: tactic) = fun (asm,gl) -> PURE_REWRITE_TAC[UNQUOTE_CONV gl] (asm,gl);;
let (QUOTE_TO_CONSTRUCTION_TAC: tactic) = fun (asm,gl) -> PURE_REWRITE_TAC[QUOTE_TO_CONSTRUCTION_CONV gl] (asm,gl);;
