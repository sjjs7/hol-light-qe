needs "Constructions/addition.ml";;
needs "Constructions/QuotationTactics.ml";;

(*               *)
(* Term builders *)
(*               *)

let one_def = define `(One = S Zero)`;;

let thenZero = define `
  (thenZero Zero = Zero) /\
  (thenZero (S Zero) = S (S Zero)) /\
  (thenZero (S (S x)) = add_unary (S (S x)) (S (S x)))`;;

let thenOne = define `
  (thenOne Zero = S Zero) /\
  (thenOne (S Zero) = S (S (S Zero))) /\
  (thenOne (S (S x)) = add_unary (add_unary (S (S x)) (S (S x))) (S Zero))`;;

(*                                                                *)
(* Classify constructions representing proper numbers of type nat *)
(*                                                                *)

let start_with_one = define `
  (start_with_one (QuoConst str ty) <=> 
  	((str = "One") /\ (ty = (TyBase "nat")))) /\
  (start_with_one (App eps1 eps2) <=> 
    (((eps1 = (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))) \/
  	(eps1 = (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))))) /\ 
	(start_with_one eps2))) /\
  (start_with_one (Abs eps1 eps2) = F) /\
  (start_with_one (QuoVar str ty) = F) /\
  (start_with_one (Quo e) = F)`;;

let proper_nat_construct = define `
  (proper_nat_construct (QuoConst str ty) <=> 
    (((str = "Zero") \/ (str = "One")) /\ (ty = (TyBase "nat")))) /\
  (proper_nat_construct (App eps1 eps2) <=> 
  	(((eps1 = (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))) \/
  	(eps1 = (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))))) /\ 
    proper_nat_construct eps2) /\
	(start_with_one eps2)) /\
  (proper_nat_construct (Quo eps) = F) /\
  (proper_nat_construct (Abs eps1 eps2) = F) /\
  (proper_nat_construct (QuoVar str ty) = F)` ;;

(*                                                                *)
(* Addition of epsilon numbers                                    *)
(*                                                                *)

let add_ebin = define `
  (add_ebin (QuoConst "Zero" (TyBase "nat")) x = x) /\
  (add_ebin x (QuoConst "Zero" (TyBase "nat")) = x) /\
  (add_ebin (QuoConst "One" (TyBase "nat")) 
    (QuoConst "One" (TyBase "nat")) = 
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) 
    (QuoConst "One" (TyBase "nat")))) /\
  (add_ebin (QuoConst "One" (TyBase "nat")) 
  	(App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) = 
    (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x)) /\
  (add_ebin (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) 
  	(QuoConst "One" (TyBase "nat")) = 
    (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x)) /\
  (add_ebin (QuoConst "One" (TyBase "nat")) 
  	(App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) = 
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) 
    (add_ebin (QuoConst "One" (TyBase "nat")) x))) /\
  (add_ebin (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) 
  	(QuoConst "One" (TyBase "nat")) = 
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) 
    (add_ebin (QuoConst "One" (TyBase "nat")) x))) /\
  (add_ebin (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) 
  	(App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) y) =
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) 
    (add_ebin x y))) /\
  (add_ebin (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) 
  	(App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) y) =
    (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) 
    (add_ebin x y))) /\
  (add_ebin (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) 
  	(App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) y) =
    (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) 
    (add_ebin x y))) /\
  (add_ebin (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) 
  	(App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) y) =
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) 
    (add_ebin (QuoConst "One" (TyBase "nat")) (add_ebin x y))))`;; 


(* Lemmas regarding constructions of nats *)

let remove_one = prove(
  `!x:nat. add_unary One (thenZero x) = thenOne x`,
  MATCH_MP_TAC(nat_induct) THEN
  REWRITE_TAC[thenZero;one_def;thenOne;add_unary] THEN
  MATCH_MP_TAC(nat_induct) THEN
  REWRITE_TAC[thenZero;one_def;thenOne;add_unary] THEN 
  GEN_TAC THEN 
  REPEAT DISCH_TAC THEN 
  REWRITE_TAC[SPECL [`(Zero):nat`;`(add_unary (S (S a)) a):nat`] take_s;id_of_plus]
  );;

let carry_one = prove(
  `!x:nat. add_unary One (thenOne x) = thenZero (add_unary One x)`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenOne; thenZero;one_def;add_unary] THEN 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenOne; thenZero;one_def;add_unary] THEN 
  GEN_TAC THEN 
  REPEAT DISCH_TAC THEN 
  REWRITE_TAC[take_s;add_unary;id_of_plus]
  );;

let ebin_sym_add = prove(
  `!x:epsilon. !y:epsilon. proper_nat_construct x /\ proper_nat_construct y ==> 
  add_ebin x y = add_ebin y x`,
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[proper_nat_construct;IMP_CONJ] THEN 
  CONJ_TAC THEN
  GEN_TAC THEN 
  GEN_TAC THENL
  [MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[proper_nat_construct;IMP_CONJ] THEN 
  CONJ_TAC THEN 
  REPEAT GEN_TAC THENL
  [REPEAT DISCH_TAC THEN 
  DISJ_CASES_TAC(ASSUME `a0 = "Zero" \/ a0 = "One"`) THEN 
  ASM_REWRITE_TAC[add_ebin] THEN 
  DISJ_CASES_TAC(ASSUME `a0' = "Zero" \/ a0' = "One"`) THEN 
  ASM_REWRITE_TAC[add_ebin]
  ;REPEAT DISCH_TAC THEN 
  DISJ_CASES_TAC(ASSUME `a0 = "Zero" \/ a0 = "One"`) THEN
  ASM_REWRITE_TAC[add_ebin] THEN
  DISJ_CASES_TAC(ASSUME `a0' =
  QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
  a0' = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THEN 
  ASM_REWRITE_TAC[add_ebin] 
  ]
  ;REPEAT DISCH_TAC THEN 
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[proper_nat_construct;IMP_CONJ] THEN 
  CONJ_TAC THEN 
  REPEAT GEN_TAC THEN 
  REPEAT DISCH_TAC THENL
  [DISJ_CASES_TAC(ASSUME `a0' = "Zero" \/ a0' = "One"`) THEN 
  ASM_REWRITE_TAC[add_ebin] THEN 
  DISJ_CASES_TAC(ASSUME `a0 = 
  QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
  a0 = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THEN 
  ASM_REWRITE_TAC[add_ebin]
  ;DISJ_CASES_TAC(ASSUME `a0 = 
  QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
  a0 = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THEN 
  DISJ_CASES_TAC(ASSUME `a0' =
  QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
  a0' = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THEN 
  ASM_REWRITE_TAC[add_ebin] THEN
  MP_TAC(SPEC `a1':epsilon` 
  (ASSUME `!y. proper_nat_construct a1
  ==> proper_nat_construct y
  ==> add_ebin a1 y = add_ebin y a1`)) THEN 
  REWRITE_TAC[ASSUME `proper_nat_construct a1`;ASSUME `proper_nat_construct a1'`] THEN
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[]
  ] 
  ]
  );;

let take_out_S = prove(
  `!x:nat. thenZero (S x) = S (S (add_unary x x))`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[add_unary;thenZero;take_s]
  );;

let take_out_s_thenOne = prove(
  `!x:nat. thenOne (S x) = S (S (S (add_unary x x)))`,
  MATCH_MP_TAC(nat_induct) THEN
  REWRITE_TAC[add_unary;thenOne;take_s]
  );;

let add_one_even = prove(
  `!x:nat. S (thenZero x) = thenOne x`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;thenOne] THEN 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;thenOne;take_s;add_unary]
  );;


let add_even = prove(
  `!x:nat. !y:nat. thenZero (add_unary x y) = 
  add_unary (thenZero x) (thenZero y)`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;id_of_plus] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;add_unary;take_s] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN
  REWRITE_TAC[take_out_S;take_s;add_unary;assoc_add] THEN 
  REWRITE_TAC[SYM(SPECL [`a:nat`;`a':nat`;`a:nat`] assoc_add)] THEN 
  MP_TAC(SPECL [`a':nat`;`a:nat`] sym_add) THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  REWRITE_TAC[assoc_add]
  );;

let add_even_odd = prove(
  `!x:nat. !y:nat. thenOne (add_unary x y) = 
  add_unary (thenZero x) (thenOne y)`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;thenOne;id_of_plus] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;add_unary;thenOne;add_one_even] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN
  REWRITE_TAC[take_out_s_thenOne;add_unary;take_s;take_out_S] THEN
  MP_TAC(SYM(SPECL [`a:nat`;`a':nat`;`(add_unary a a'):nat`] assoc_add)) THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_TAC(SPECL [`a':nat`;`(add_unary a a'):nat`] sym_add) THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  REWRITE_TAC[assoc_add]
  );;

let add_odd_even = prove(
  `!x:nat. !y:nat. thenOne (add_unary x y) = 
  add_unary (thenOne x) (thenZero y)`,
  REPEAT GEN_TAC THEN 
  MP_TAC(SPECL [`x:nat`;`y:nat`] sym_add) THEN
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  REWRITE_TAC[add_even_odd;sym_add]
  );;

let odd_to_even = prove(
  `!x:nat. S (thenOne x) = thenZero (S x)`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;thenOne] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[take_out_s_thenOne;add_unary;take_s]
  );;



(* Lemma 1 *)
let lemma1 = prove(
  `!x:epsilon. proper_nat_construct x ==> 
  isExprType x (TyBase "nat")`,
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[proper_nat_construct] THEN
  CONJ_TAC THEN 
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN 
  REWRITE_TAC[isExprType] THEN
  REPEAT DISCH_TAC THEN 
  IS_EXPR_TYPE_TAC THEN 
  DISJ_CASES_TAC(ASSUME 
    `a0 = QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) 
  	\/ a0 = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THEN
  ASM_REWRITE_TAC[
    ep_constructor;combinatoryType;isFunction;headFunc;isExpr;stripFunc] THEN 
  MP_TAC(ASSUME 
    `proper_nat_construct a1 ==> 
  	isExpr a1 /\ combinatoryType a1 = TyBase "nat"`) THEN
  REWRITE_TAC[ASSUME `proper_nat_construct a1`] THEN 
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[]);; 


let lemma3 = prove(
  `!x:epsilon. start_with_one x ==> 
  start_with_one (add_ebin (QuoConst "One" (TyBase "nat")) x)`,
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[start_with_one] THEN
  CONJ_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT DISCH_TAC THENL
  [ASM_REWRITE_TAC[add_ebin;start_with_one]
  ;DISJ_CASES_TAC(ASSUME 
    `a0 = QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
    a0 = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THENL
  [ASM_REWRITE_TAC[add_ebin;start_with_one]
  ;ASM_REWRITE_TAC[add_ebin;start_with_one] THEN 
  MP_TAC(ASSUME `start_with_one a1
    ==> start_with_one (add_ebin (QuoConst "One" (TyBase "nat")) a1)`) THEN
  REWRITE_TAC[ASSUME `start_with_one a1`]
  ] 
  ]
  );;

let lemma4 = prove( 
  `!x:epsilon. proper_nat_construct x ==> 
  proper_nat_construct (add_ebin (QuoConst "One" (TyBase "nat")) x)`,
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[proper_nat_construct] THEN
  CONJ_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT DISCH_TAC THENL
  [DISJ_CASES_TAC(ASSUME `a0 = "Zero" \/ a0 = "One"`) THEN
  ASM_REWRITE_TAC[add_ebin;proper_nat_construct;start_with_one]
  ;DISJ_CASES_TAC(ASSUME 
    `a0 = QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
    a0 = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THEN
  ASM_REWRITE_TAC[add_ebin;proper_nat_construct] THEN 
  MP_TAC(ASSUME 
  	`proper_nat_construct a1 ==> 
  	proper_nat_construct (add_ebin (QuoConst "One" (TyBase "nat")) a1)`) THEN 
  MP_TAC(SPEC `a1:epsilon` lemma3) THEN 
  REWRITE_TAC[ASSUME `proper_nat_construct a1`;ASSUME `start_with_one a1`] THEN 
  REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[]
  ]
  );;

let lemma5 = prove(
  `!x:epsilon. !y:epsilon. start_with_one x /\ 
  start_with_one y ==> start_with_one (add_ebin x y)`,
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[start_with_one] THEN 
  CONJ_TAC THENL 
  [REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_TAC(SPEC `y:epsilon` lemma3) THEN
  REWRITE_TAC[ASSUME `start_with_one y`]
  ;REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MATCH_MP_TAC(lth) THEN
  REWRITE_TAC[start_with_one] THEN
  CONJ_TAC THEN 
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT DISCH_TAC THENL
  [DISJ_CASES_TAC(ASSUME 
    `a0 = QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
    a0 = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THEN
  ASM_REWRITE_TAC[add_ebin;start_with_one] THEN 
  MP_TAC(SPEC `a1:epsilon` lemma3) THEN 
  REWRITE_TAC[ASSUME `start_with_one a1`]
  ;DISJ_CASES_TAC(ASSUME 
    `a0' = QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
    a0' = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THEN 
  DISJ_CASES_TAC(ASSUME 
    `a0 = QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
    a0 = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THEN 
  ASM_REWRITE_TAC[add_ebin;start_with_one] THEN
  MP_TAC(SPEC `a1':epsilon` (ASSUME 
    `!y. start_with_one a1
    ==> start_with_one y
    ==> start_with_one (add_ebin a1 y)`)) THEN 
  REWRITE_TAC[ASSUME `start_with_one a1`; ASSUME `start_with_one a1'`] THEN 
  DISCH_TAC THEN 
  MP_TAC(SPEC `add_ebin (a1:epsilon) (a1':epsilon)` lemma3) THEN 
  REWRITE_TAC[ASSUME `start_with_one (add_ebin a1 a1')`]
  ]
  ]
  );;

let lemma6 = prove(
  `!x:epsilon. !y:epsilon. proper_nat_construct x /\ 
  proper_nat_construct y ==> proper_nat_construct (add_ebin x y)`,
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[proper_nat_construct] THEN 
  CONJ_TAC THENL 
  [GEN_TAC THEN
  GEN_TAC THEN 
  MATCH_MP_TAC(lth) THEN
  REWRITE_TAC[proper_nat_construct] THEN 
  CONJ_TAC THENL 
  [REWRITE_TAC[IMP_CONJ] THEN
  REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN
  DISJ_CASES_TAC(ASSUME `a0 = "Zero" \/ a0 = "One"`) THENL
  [ASM_REWRITE_TAC[add_ebin;proper_nat_construct] 
  ;DISJ_CASES_TAC(ASSUME `a0' = "Zero" \/ a0' = "One"`) THEN
  ASM_REWRITE_TAC[add_ebin;proper_nat_construct;start_with_one]
  ]
  ;REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT DISCH_TAC THEN 
  DISJ_CASES_TAC(ASSUME `a0 = "Zero" \/ a0 = "One"`) THENL
  [ASM_REWRITE_TAC[add_ebin;proper_nat_construct]
  ;DISJ_CASES_TAC(ASSUME 
    `a0' = QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
    a0' = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THENL
  [ASM_REWRITE_TAC[add_ebin;proper_nat_construct;start_with_one]
  ;ASM_REWRITE_TAC[add_ebin;proper_nat_construct;start_with_one] THEN
  MP_TAC(SPEC `a1':epsilon` lemma3) THEN 
  MP_TAC(ASSUME 
    `a0 = "Zero" \/ a0 = "One"
    ==> a1 = TyBase "nat"
    ==> proper_nat_construct a1'
    ==> proper_nat_construct (add_ebin (QuoConst a0 a1) a1')`) THEN 
  REWRITE_TAC[
    ASSUME `proper_nat_construct a1'`; 
    ASSUME `start_with_one a1'`; 
    ASSUME `a0 = "One"`; 
    ASSUME `a1 = TyBase "nat"`] THEN 
  REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[]
  ] 
  ]
  ]
  ;REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[proper_nat_construct] THEN 
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN 
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  DISJ_CASES_TAC(ASSUME 
    `a0 = QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
    a0 = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THEN
  DISJ_CASES_TAC(ASSUME `a0' = "Zero" \/ a0' = "One"`) THEN 
  ASM_REWRITE_TAC[add_ebin;proper_nat_construct] THEN 
  MP_TAC(SPEC `a1:epsilon` lemma3) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_TAC(SPEC `a1:epsilon` lemma4) THEN
  ASM_REWRITE_TAC[]
  ;REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  DISJ_CASES_TAC(ASSUME 
    `a0 = QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
    a0 = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THEN 
  DISJ_CASES_TAC(ASSUME 
    `a0' = QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
    a0' = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THEN
  ASM_REWRITE_TAC[add_ebin;proper_nat_construct] THEN 
  ASM_REWRITE_TAC[add_ebin;proper_nat_construct] THEN 
  MP_TAC(SPEC `a1':epsilon` (ASSUME 
  	`!y. proper_nat_construct a1 ==> 
  	proper_nat_construct y ==> 
  	proper_nat_construct (add_ebin a1 y)`)) THEN
  MP_TAC(SPECL [`a1:epsilon`;`a1':epsilon`] lemma5) THEN 
  REWRITE_TAC[
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct a1'`;
    ASSUME `start_with_one a1`;
    ASSUME `start_with_one a1'`] THEN 
  REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `add_ebin (a1:epsilon) (a1':epsilon)` lemma3) THEN
  MP_TAC(SPEC `add_ebin (a1:epsilon) (a1':epsilon)` lemma4) THEN 
  REWRITE_TAC[
    ASSUME `start_with_one (add_ebin a1 a1')`; 
    ASSUME `proper_nat_construct (add_ebin a1 a1')`] THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[]
  ]
  ] 
  );;

  
let thm1 = prove(
  `!x:epsilon. !y:epsilon. proper_nat_construct x /\ proper_nat_construct y 
  ==> isExprType(add_ebin x y) (TyBase "nat")`,
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [`x:epsilon`;`y:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  MP_TAC(SPEC `(add_ebin x y):epsilon` lemma1) THEN 
  ASM_REWRITE_TAC[]
  );;
  
let thm2 = prove(
  `!x:epsilon. !str:string. !ty:type. proper_nat_construct x 
  ==> ~isFreeIn (QuoVar str ty) x`,
  MATCH_MP_TAC(lth) THEN
  REWRITE_TAC[proper_nat_construct;isFreeIn] THEN 
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  GEN_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  DISCH_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[DE_MORGAN_THM] THEN 
  MP_TAC(SPECL [`str:string`;`ty:type`] (ASSUME 
    `!str ty. proper_nat_construct a1 
    ==> ~isFreeIn (QuoVar str ty) a1`)) THEN 
  REWRITE_TAC[ASSUME `proper_nat_construct a1`] THEN
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  DISJ_CASES_TAC(ASSUME 
    `a0 = QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
    a0 = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THEN 
  ASM_REWRITE_TAC[isFreeIn] 
  );;


(* ADDITION TACTICS *)

(* when proper_nat_construct x is an assumption, adds isExprType x nat to assumptions *)
let PROPER_TYPE_TAC tm = 
  MP_TAC(SPEC tm lemma1) THEN 
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC;; 

(* adds ~isFreeIn (QuoVar str ty) tm to assumptions *)
let PROPER_NOT_FREE_TAC tm str ty = 
  SUBGOAL_THEN (rand(concl (SPECL [tm;str;ty] thm2))) ASSUME_TAC THEN 
  MP_TAC(SPECL [tm;str;ty] thm2) THEN 
  ASM_REWRITE_TAC[proper_nat_construct;start_with_one] THEN 
  REWRITE_TAC[isExprType;isExpr];;

(* when isExprType and notFreeIn thms are assumtions *)
let NAT_BETA_EVAL_RED tm = 
  match tm with 
    | Comb(Abs(v, Eval(ep,et)),arg) -> 
        ((SUBGOAL_THEN (rand(concl(BETA_REDUCE_EVAL v arg ep et))) ASSUME_TAC) THEN  
        MP_TAC(BETA_REDUCE_EVAL v arg ep et) THEN 
        ASM_REWRITE_TAC[])
    | _ -> failwith "wrong input";;


  
(* Trivial NOT-EFFECTIVE-IN statements- used for instantiating into induction thms *)
let ne1 = NOT_FREE_ABS_NOT_EFFECTIVE_CONV 
  `x:epsilon` `proper_nat_construct (x:epsilon) ==> 
  (\a0:string. (eval (x:epsilon) to (nat))) (w:string) = 
  eval (\a0. x) w to (nat)` `z:epsilon`;;
addNotEff ne1;;  

let ne21 = NOT_FREE_ABS_NOT_EFFECTIVE_CONV 
  `x:epsilon` `proper_nat_construct (x:epsilon) ==> 
  (\a1:type. (eval (x:epsilon) to (nat))) (w:type) = 
  eval (\a1. x) w to (nat)` `z:epsilon`;;
addNotEff ne21;; 

(* lemmas to simplify first instantiation *)
let beta_red1 = prove(
  `!j:epsilon. proper_nat_construct j ==> 
  (\a0:string. (eval j to (nat))) (w:string) = eval (\a0. j) w to (nat)`,
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MP_TAC(SPEC `j:epsilon` lemma1) THEN 
  REWRITE_TAC[ASSUME `proper_nat_construct j`] THEN 
  DISCH_TAC THEN 
  MP_TAC(BETA_REDUCE_EVAL `a0:string` `w:string` `j:epsilon` `:nat`) THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_TAC(SPECL [`j:epsilon`;`"a0":string`;
    `(TyMonoCons "list" (TyBase "char")):type`] thm2) THEN 
  REWRITE_TAC[ASSUME `proper_nat_construct j`] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[]);;

let taut_lemma = 
  TAUT `!p:bool. !q:bool. !r:bool. ((p ==> q) = (p ==> r)) <=> (p ==> (q = r))`;;

let fin_beta_red1 = prove( 
  `(proper_nat_construct (x:epsilon) /\ proper_nat_construct (y:epsilon) ==> 
  (\(a0:string). (eval (add_ebin (x:epsilon) (y:epsilon)) to (nat))) (w:string) =
  add_unary ((\(a0:string). (eval (x:epsilon) to (nat))) (w:string)) 
  ((\(a0:string). (eval (y:epsilon) to (nat))) (w:string))) =
  (proper_nat_construct (x:epsilon) /\ proper_nat_construct (y:epsilon) ==> 
  (eval (add_ebin (x:epsilon) (y:epsilon)) to (nat)) =
  add_unary (eval (x:epsilon) to (nat)) (eval (y:epsilon) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`x:epsilon`;`y:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  MP_TAC(SPEC `x:epsilon` beta_red1) THEN 
  MP_TAC(SPEC `y:epsilon` beta_red1) THEN 
  MP_TAC(SPEC `(add_ebin x y):epsilon` beta_red1) THEN
  PROPER_TYPE_TAC(`x:epsilon`) THEN 
  PROPER_TYPE_TAC(`y:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin x y):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `y:epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `x:epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(add_ebin x y):epsilon` `"j"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) (y:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) (x:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) ((add_ebin x y):epsilon)`) THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[]
  );;

let beta_red2 = prove(
  `!j:epsilon. proper_nat_construct j ==> 
  (\a1:type. (eval j to (nat))) (w:type) = eval (\a0. j) w to (nat)`,
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MP_TAC(SPEC `j:epsilon` lemma1) THEN 
  REWRITE_TAC[ASSUME `proper_nat_construct j`] THEN 
  DISCH_TAC THEN 
  MP_TAC(BETA_REDUCE_EVAL `a1:type` `w:type` `j:epsilon` `:nat`) THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_TAC(SPECL [`j:epsilon`;`"a1":string`;`(TyBase "type"):type`] thm2) THEN 
  REWRITE_TAC[ASSUME `proper_nat_construct j`] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[]);;

let fin_beta_red2 = prove( 
  `(proper_nat_construct (x:epsilon) /\ proper_nat_construct (y:epsilon) ==> 
  (\(a1:type). (eval (add_ebin (x:epsilon) (y:epsilon)) to (nat))) (w:type) =
  add_unary ((\(a1:type). (eval (x:epsilon) to (nat))) (w:type)) 
  ((\(a1:type). (eval (y:epsilon) to (nat))) (w:type))) =
  (proper_nat_construct (x:epsilon) /\ proper_nat_construct (y:epsilon) ==> 
  (eval (add_ebin (x:epsilon) (y:epsilon)) to (nat)) =
  add_unary (eval (x:epsilon) to (nat)) (eval (y:epsilon) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`x:epsilon`;`y:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  MP_TAC(SPEC `x:epsilon` beta_red2) THEN 
  MP_TAC(SPEC `y:epsilon` beta_red2) THEN 
  MP_TAC(SPEC `(add_ebin x y):epsilon` beta_red2) THEN
  PROPER_TYPE_TAC(`x:epsilon`) THEN 
  PROPER_TYPE_TAC(`y:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin x y):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `y:epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `x:epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(add_ebin x y):epsilon` `"j"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) (y:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) (x:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) ((add_ebin x y):epsilon)`) THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[]
  );;
 


(* lemmas to simplify second instantiation *)
let beta_red3 = 
  EQ_MP (ALPHA (concl beta_red1) `!j:epsilon. proper_nat_construct j ==> 
  (\b0:string. (eval j to (nat))) (w:string) = eval (\a0. j) w to (nat)`) beta_red1;;

let fin_beta_red3 = prove( 
  `(proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct (y:epsilon)
  ==> (\b0:string. (eval (add_ebin (QuoConst a0 a1) (y:epsilon)) to (nat))) (w:string) =
  add_unary ((\b0:string. (eval (QuoConst a0 a1) to (nat))) (w:string))
  ((\b0:string. (eval (y:epsilon) to (nat))) (w:string))) =
  (proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct (y:epsilon)
  ==> (eval (add_ebin (QuoConst a0 a1) (y:epsilon)) to (nat)) =
  add_unary (eval (QuoConst a0 a1) to (nat)) (eval (y:epsilon) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`(QuoConst a0 a1):epsilon`;`y:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  MP_TAC(SPEC `(QuoConst a0 a1):epsilon` beta_red3) THEN 
  MP_TAC(SPEC `y:epsilon` beta_red3) THEN 
  MP_TAC(SPEC `(add_ebin (QuoConst a0 a1) y):epsilon` beta_red3) THEN
  PROPER_TYPE_TAC(`(QuoConst a0 a1):epsilon`) THEN 
  PROPER_TYPE_TAC(`y:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (QuoConst a0 a1) y):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `y:epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(QuoConst a0 a1):epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(add_ebin (QuoConst a0 a1) y):epsilon` `"j"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) (y:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) ((QuoConst a0 a1):epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) ((add_ebin (QuoConst a0 a1) y):epsilon)`) THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[]
  );;

let beta_red4 = 
  EQ_MP (ALPHA (concl beta_red2) `!j:epsilon. proper_nat_construct j ==> 
  (\b1:type. (eval j to (nat))) (w:type) = eval (\a0. j) w to (nat)`) beta_red2;;

let fin_beta_red4 = prove(
  `(proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
  ==> (\b1. (eval (add_ebin (QuoConst a0 a1) y) to (nat))) (w:type) =
  add_unary ((\b1. (eval (QuoConst a0 a1) to (nat))) w)
  ((\b1. (eval (y) to (nat))) w)) =
  (proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
  ==> (eval (add_ebin (QuoConst a0 a1) y) to (nat)) =
  add_unary (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`(QuoConst a0 a1):epsilon`;`y:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  MP_TAC(SPEC `(QuoConst a0 a1):epsilon` beta_red4) THEN 
  MP_TAC(SPEC `y:epsilon` beta_red4) THEN 
  MP_TAC(SPEC `(add_ebin (QuoConst a0 a1) y):epsilon` beta_red4) THEN
  PROPER_TYPE_TAC(`(QuoConst a0 a1):epsilon`) THEN 
  PROPER_TYPE_TAC(`y:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (QuoConst a0 a1) y):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `y:epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(QuoConst a0 a1):epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(add_ebin (QuoConst a0 a1) y):epsilon` `"j"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) (y:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) ((QuoConst a0 a1):epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) ((add_ebin (QuoConst a0 a1) y):epsilon)`) THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[]
  );;

let beta_red5 = prove(
  `!j:epsilon. proper_nat_construct j ==> 
  (\b0:epsilon. (eval j to (nat))) (w:epsilon) = eval (\a0. j) w to (nat)`,
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MP_TAC(SPEC `j:epsilon` lemma1) THEN 
  REWRITE_TAC[ASSUME `proper_nat_construct j`] THEN 
  DISCH_TAC THEN 
  MP_TAC(BETA_REDUCE_EVAL `b0:epsilon` `w:epsilon` `j:epsilon` `:nat`) THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_TAC(SPECL [`j:epsilon`;`"b0":string`;`(TyBase "epsilon"):type`] thm2) THEN 
  REWRITE_TAC[ASSUME `proper_nat_construct j`] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[]);;

let fin_beta_red5 = prove(
  `(proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct (y:epsilon)
  ==> (\b0:epsilon. (eval (add_ebin (QuoConst a0 a1) (y:epsilon)) to (nat))) (w:epsilon) =
  add_unary ((\b0:epsilon. (eval (QuoConst a0 a1) to (nat))) (w:epsilon))
  ((\b0:epsilon. (eval (y:epsilon) to (nat))) (w:epsilon))) =
  (proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct (y:epsilon)
  ==> (eval (add_ebin (QuoConst a0 a1) (y:epsilon)) to (nat)) =
  add_unary (eval (QuoConst a0 a1) to (nat)) (eval (y:epsilon) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`(QuoConst a0 a1):epsilon`;`y:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  MP_TAC(SPEC `(QuoConst a0 a1):epsilon` beta_red5) THEN 
  MP_TAC(SPEC `y:epsilon` beta_red5) THEN 
  MP_TAC(SPEC `(add_ebin (QuoConst a0 a1) y):epsilon` beta_red5) THEN
  PROPER_TYPE_TAC(`(QuoConst a0 a1):epsilon`) THEN 
  PROPER_TYPE_TAC(`y:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (QuoConst a0 a1) y):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `y:epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(QuoConst a0 a1):epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(add_ebin (QuoConst a0 a1) y):epsilon` `"j"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) (y:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) ((QuoConst a0 a1):epsilon)`) THEN 
  NAT_BETA_EVAL_RED(
  	`(\j:epsilon. (eval (j) to (nat))) ((add_ebin (QuoConst a0 a1) y):epsilon)`) THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[]
  );;

let beta_red6 = 
  EQ_MP (ALPHA (concl beta_red5)`!j:epsilon. proper_nat_construct j ==> 
  (\a0:epsilon. (eval j to (nat))) (w:epsilon) = eval (\a0. j) w to (nat)`) beta_red5;;

let fin_beta_red6 = prove(
  `(proper_nat_construct (x:epsilon) /\ proper_nat_construct (y:epsilon) ==> 
  (\(a0:epsilon). (eval (add_ebin (x:epsilon) (y:epsilon)) to (nat))) (w:epsilon) =
  add_unary ((\(a0:epsilon). (eval (x:epsilon) to (nat))) (w:epsilon)) 
  ((\(a0:epsilon). (eval (y:epsilon) to (nat))) (w:epsilon))) =
  (proper_nat_construct (x:epsilon) /\ proper_nat_construct (y:epsilon) ==> 
  (eval (add_ebin (x:epsilon) (y:epsilon)) to (nat)) =
  add_unary (eval (x:epsilon) to (nat)) (eval (y:epsilon) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`x:epsilon`;`y:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  MP_TAC(SPEC `x:epsilon` beta_red6) THEN 
  MP_TAC(SPEC `y:epsilon` beta_red6) THEN 
  MP_TAC(SPEC `(add_ebin x y):epsilon` beta_red6) THEN
  PROPER_TYPE_TAC(`x:epsilon`) THEN 
  PROPER_TYPE_TAC(`y:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin x y):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `y:epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `x:epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(add_ebin x y):epsilon` `"j"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) (y:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) (x:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) ((add_ebin x y):epsilon)`) THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[]
  );;

let fin_beta_red7 = prove(
  `(proper_nat_construct (App a0 a1) ==> proper_nat_construct (y:epsilon)
  ==> (\b0:string. (eval (add_ebin (App a0 a1) (y:epsilon)) to (nat))) (w:string) =
  add_unary ((\b0:string. (eval (App a0 a1) to (nat))) (w:string))
  ((\b0:string. (eval (y:epsilon) to (nat))) (w:string))) =
  (proper_nat_construct (App a0 a1) ==> proper_nat_construct (y:epsilon)
  ==> (eval (add_ebin (App a0 a1) (y:epsilon)) to (nat)) =
  add_unary (eval (App a0 a1) to (nat)) (eval (y:epsilon) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`(App a0 a1):epsilon`;`y:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  MP_TAC(SPEC `(App a0 a1):epsilon` beta_red3) THEN 
  MP_TAC(SPEC `y:epsilon` beta_red3) THEN 
  MP_TAC(SPEC `(add_ebin (App a0 a1) y):epsilon` beta_red3) THEN
  PROPER_TYPE_TAC(`(App a0 a1):epsilon`) THEN 
  PROPER_TYPE_TAC(`y:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (App a0 a1) y):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `y:epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(App a0 a1):epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(add_ebin (App a0 a1) y):epsilon` `"j"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) (y:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) ((App a0 a1):epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) ((add_ebin (App a0 a1) y):epsilon)`) THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[]
  );;

let fin_beta_red8 = prove(
  `(proper_nat_construct (App a0 a1) ==> proper_nat_construct y
  ==> (\b1. (eval (add_ebin (App a0 a1) y) to (nat))) (w:type) =
  add_unary ((\b1. (eval (App a0 a1) to (nat))) w)
  ((\b1. (eval (y) to (nat))) w)) =
  (proper_nat_construct (App a0 a1) ==> proper_nat_construct y
  ==> (eval (add_ebin (App a0 a1) y) to (nat)) =
  add_unary (eval (App a0 a1) to (nat)) (eval (y) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`(App a0 a1):epsilon`;`y:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  MP_TAC(SPEC `(App a0 a1):epsilon` beta_red4) THEN 
  MP_TAC(SPEC `y:epsilon` beta_red4) THEN 
  MP_TAC(SPEC `(add_ebin (App a0 a1) y):epsilon` beta_red4) THEN
  PROPER_TYPE_TAC(`(App a0 a1):epsilon`) THEN 
  PROPER_TYPE_TAC(`y:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (App a0 a1) y):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `y:epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(App a0 a1):epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(add_ebin (App a0 a1) y):epsilon` `"j"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) (y:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) ((App a0 a1):epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) ((add_ebin (App a0 a1) y):epsilon)`) THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[]
  );;

let fin_beta_red9 = prove( 
  `(proper_nat_construct (App a0 a1) ==> proper_nat_construct (y:epsilon)
  ==> (\b0:epsilon. (eval (add_ebin (App a0 a1) (y:epsilon)) to (nat))) (w:epsilon) =
  add_unary ((\b0:epsilon. (eval (App a0 a1) to (nat))) (w:epsilon))
  ((\b0:epsilon. (eval (y:epsilon) to (nat))) (w:epsilon))) =
  (proper_nat_construct (App a0 a1) ==> proper_nat_construct (y:epsilon)
  ==> (eval (add_ebin (App a0 a1) (y:epsilon)) to (nat)) =
  add_unary (eval (App a0 a1) to (nat)) (eval (y:epsilon) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`(App a0 a1):epsilon`;`y:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  MP_TAC(SPEC `(App a0 a1):epsilon` beta_red5) THEN 
  MP_TAC(SPEC `y:epsilon` beta_red5) THEN 
  MP_TAC(SPEC `(add_ebin (App a0 a1) y):epsilon` beta_red5) THEN
  PROPER_TYPE_TAC(`(App a0 a1):epsilon`) THEN 
  PROPER_TYPE_TAC(`y:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (App a0 a1) y):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `y:epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(App a0 a1):epsilon` `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(add_ebin (App a0 a1) y):epsilon` `"j"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) (y:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) ((App a0 a1):epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`(\j:epsilon. (eval (j) to (nat))) ((add_ebin (App a0 a1) y):epsilon)`) THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[]
  );;





(* Needed to do first induction *)
let ind_1 = NOT_FREE_ABS_NOT_EFFECTIVE_CONV `x:epsilon` 
  `!y:epsilon. (((proper_nat_construct (x:epsilon)) /\ 
  (proper_nat_construct (y:epsilon))) ==> 
  (eval (add_ebin x y) to (nat) = 
  add_unary (eval x to (nat)) (eval y to (nat))))` `w:epsilon`;;
addNotEff ind_1;;

let a0_ne = prove(
  mk_not_effective_in `a0:string` 
  `\x:epsilon. !y:epsilon. proper_nat_construct x /\ proper_nat_construct y ==>
  (eval (add_ebin x y) to (nat)) = 
  add_unary (eval (x) to (nat)) (eval (y) to (nat))` `w:string`,
  GEN_TAC THEN 
  REWRITE_TAC[BETA_RED_BY_SUB `(\a0:string. \x:epsilon. !y:epsilon. 
  	proper_nat_construct x /\ proper_nat_construct y ==> 
    (eval (add_ebin x y) to (nat)) = 
    add_unary (eval (x) to (nat)) (eval (y) to (nat))) (w:string)`] THEN 
  REWRITE_TAC[fin_beta_red1]
  );;
addNotEff a0_ne;;

let a1_ne = prove(
  mk_not_effective_in `a1:type` 
  `\x:epsilon. !y:epsilon. proper_nat_construct x /\ proper_nat_construct y ==>
  (eval (add_ebin x y) to (nat)) = 
  add_unary (eval (x) to (nat)) (eval (y) to (nat))` `w:type`,
  GEN_TAC THEN 
  REWRITE_TAC[BETA_RED_BY_SUB `(\a1:type. \x:epsilon. !y:epsilon. 
  	proper_nat_construct x /\ proper_nat_construct y ==> 
    (eval (add_ebin x y) to (nat)) = 
    add_unary (eval (x) to (nat)) (eval (y) to (nat))) (w:type)`] THEN 
  REWRITE_TAC[fin_beta_red2]
  );;
addNotEff a1_ne;;

let a0_eps_ne = prove(
  mk_not_effective_in `a0:epsilon` 
  `\x. !y. proper_nat_construct x /\ proper_nat_construct y
  ==> (eval (add_ebin x y) to (nat)) =
  add_unary (eval (x) to (nat)) (eval (y) to (nat))` `w:epsilon`,
  GEN_TAC THEN 
  REWRITE_TAC[BETA_RED_BY_SUB `(\a0:epsilon. \x:epsilon. !y:epsilon. 
    proper_nat_construct x /\ proper_nat_construct y
    ==> (eval (add_ebin x y) to (nat)) =
    add_unary (eval (x) to (nat)) (eval (y) to (nat))) (w:epsilon)`] THEN 
  REWRITE_TAC[fin_beta_red6]
  );;
addNotEff a0_eps_ne;;

let a1_eps_ne = 
  let tm = (mk_not_effective_in `a1:epsilon` 
  	`\x. !y. proper_nat_construct x /\ proper_nat_construct y
    ==> (eval (add_ebin x y) to (nat)) =
    add_unary (eval (x) to (nat)) (eval (y) to (nat))` `w:epsilon`) in
  EQ_MP (ALPHA (concl a0_eps_ne) tm) a0_eps_ne;;
addNotEff a1_eps_ne;;

let a_eps_ne = 
  let tm = (mk_not_effective_in `a:epsilon` 
    `\x. !y. proper_nat_construct x /\ proper_nat_construct y
    ==> (eval (add_ebin x y) to (nat)) =
    add_unary (eval (x) to (nat)) (eval (y) to (nat))` `w:epsilon`) in
  EQ_MP (ALPHA (concl a0_eps_ne) tm) a0_eps_ne;;
addNotEff a_eps_ne;;

(* Second Induction(s) *)

(* Need an induction theorem with different bound variables for second inductions *)
let eps_alt_ind = 
  EQ_MP (ALPHA (concl lth) 
  `!P. (!b0 b1. P (QuoVar b0 b1)) /\ (!b0 b1. P (QuoConst b0 b1)) /\
  (!b0 b1. P b0 /\ P b1 ==> P (App b0 b1)) /\
  (!b0 b1. P b0 /\ P b1 ==> P (Abs b0 b1)) /\
  (!b. P b ==> P (Quo b)) ==> (!b. P b)`) lth;;

let ind_y1 = NOT_FREE_ABS_NOT_EFFECTIVE_CONV `y:epsilon` 
  `proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
  ==> (eval (add_ebin (QuoConst a0 a1) y) to (nat)) =
  add_unary (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))` `w:epsilon`;;
addNotEff ind_y1;;

let b0_ne = prove(
  mk_not_effective_in `b0:string` 
  `\y. proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
  ==> (eval (add_ebin (QuoConst a0 a1) y) to (nat)) =
  add_unary (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))` `w:string`,
  GEN_TAC THEN 
  REWRITE_TAC[BETA_RED_BY_SUB `(\b0:string. \y:epsilon. 
    proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
    ==> (eval (add_ebin (QuoConst a0 a1) y) to (nat)) =
    add_unary (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))) (w:string)`] THEN 
  REWRITE_TAC[fin_beta_red3]
  );;
addNotEff b0_ne;;

let b1_ne = prove(
  mk_not_effective_in `b1:type` 
  `\y. proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
  ==> (eval (add_ebin (QuoConst a0 a1) y) to (nat)) =
  add_unary (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))` `w:type`,
  GEN_TAC THEN 
  REWRITE_TAC[BETA_RED_BY_SUB `(\b1:type. \y:epsilon. 
    proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
    ==> (eval (add_ebin (QuoConst a0 a1) y) to (nat)) =
    add_unary (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))) (w:type)`] THEN 
  REWRITE_TAC[fin_beta_red4]
  );;
addNotEff b1_ne;;


let b0_eps_ne = prove(
  mk_not_effective_in `b0:epsilon` 
  `\y. proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
  ==> (eval (add_ebin (QuoConst a0 a1) y) to (nat)) =
  add_unary (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))` `w:epsilon`,
  GEN_TAC THEN 
  REWRITE_TAC[BETA_RED_BY_SUB `(\b0:epsilon. \y:epsilon. 
    proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
    ==> (eval (add_ebin (QuoConst a0 a1) y) to (nat)) =
    add_unary (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))) (w:epsilon)`] THEN 
  REWRITE_TAC[fin_beta_red5]
  );;
addNotEff b0_eps_ne;;

let b1_eps_ne = 
  let tm = (mk_not_effective_in `b1:epsilon` 
    `\y. proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
    ==> (eval (add_ebin (QuoConst a0 a1) y) to (nat)) =
    add_unary (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))` `w:epsilon`) 
  in
  EQ_MP (ALPHA (concl b0_eps_ne) tm) b0_eps_ne;;
addNotEff b1_eps_ne;;

let ind_y2 = NOT_FREE_ABS_NOT_EFFECTIVE_CONV `y:epsilon` 
  `proper_nat_construct (App a0 a1)
  ==> proper_nat_construct y
  ==> (eval (add_ebin (App a0 a1) y) to (nat)) =
  add_unary (eval (App a0 a1) to (nat)) (eval (y) to (nat))` `w:epsilon`;;
addNotEff ind_y2;;

let b0_app_ne = prove(
  mk_not_effective_in `b0:string` 
  `\y. proper_nat_construct (App a0 a1)
  ==> proper_nat_construct y
  ==> (eval (add_ebin (App a0 a1) y) to (nat)) =
  add_unary (eval (App a0 a1) to (nat)) (eval (y) to (nat))` `w:string`,
  GEN_TAC THEN 
  REWRITE_TAC[BETA_RED_BY_SUB `(\b0:string. \y. proper_nat_construct (App a0 a1)
    ==> proper_nat_construct y
    ==> (eval (add_ebin (App a0 a1) y) to (nat)) =
    add_unary (eval (App a0 a1) to (nat)) (eval (y) to (nat))) (w:string)`] THEN 
  REWRITE_TAC[fin_beta_red7]
  );;
addNotEff b0_app_ne;;

let b1_app_ne = prove(
  mk_not_effective_in `b1:type` 
  `\y. proper_nat_construct (App a0 a1) ==> proper_nat_construct y
  ==> (eval (add_ebin (App a0 a1) y) to (nat)) =
  add_unary (eval (App a0 a1) to (nat)) (eval (y) to (nat))` `w:type`,
  GEN_TAC THEN 
  REWRITE_TAC[BETA_RED_BY_SUB `(\b1:type. \y:epsilon. 
    proper_nat_construct (App a0 a1) ==> proper_nat_construct y
    ==> (eval (add_ebin (App a0 a1) y) to (nat)) =
    add_unary (eval (App a0 a1) to (nat)) (eval (y) to (nat))) (w:type)`] THEN 
  REWRITE_TAC[fin_beta_red8]
  );;
addNotEff b1_app_ne;;

let b0_eps_app_ne = prove(
  mk_not_effective_in `b0:epsilon` 
  `\y. proper_nat_construct (App a0 a1) ==> proper_nat_construct y
  ==> (eval (add_ebin (App a0 a1) y) to (nat)) =
  add_unary (eval (App a0 a1) to (nat)) (eval (y) to (nat))` `w:epsilon`,
  GEN_TAC THEN 
  REWRITE_TAC[BETA_RED_BY_SUB 
    `(\b0:epsilon. \y:epsilon. proper_nat_construct (App a0 a1) ==> 
    proper_nat_construct y
    ==> (eval (add_ebin (App a0 a1) y) to (nat)) =
    add_unary (eval (App a0 a1) to (nat)) (eval (y) to (nat))) (w:epsilon)`] THEN 
  REWRITE_TAC[fin_beta_red9]
  );;
addNotEff b0_eps_app_ne;;

let b1_eps_app_ne = 
  let tm = (mk_not_effective_in `b1:epsilon` 
  	`\y. proper_nat_construct (App a0 a1) ==> proper_nat_construct y
    ==> (eval (add_ebin (App a0 a1) y) to (nat)) =
    add_unary (eval (App a0 a1) to (nat)) (eval (y) to (nat))` `w:epsilon`) 
  in
  EQ_MP (ALPHA (concl b0_eps_app_ne) tm) b0_eps_app_ne;;
addNotEff b1_eps_app_ne;;


(* Simplyifying lemmas *)
let x_quoconst_sub = prove( 
  `(proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct (y:epsilon)
  ==> (\x:epsilon. (eval (add_ebin x y) to (nat))) (QuoConst a0 a1) =
  add_unary ((\x:epsilon. (eval (x) to (nat))) (QuoConst a0 a1))
  ((\x:epsilon. (eval (y) to (nat))) (QuoConst a0 a1))) = 
  (proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct (y:epsilon)
  ==> (eval (add_ebin (QuoConst a0 a1) y) to (nat)) =
  add_unary (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [`(QuoConst a0 a1):epsilon`;`y:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`(QuoConst a0 a1):epsilon`) THEN 
  PROPER_TYPE_TAC(`y:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (QuoConst a0 a1) y):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `y:epsilon` `"x"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(QuoConst a0 a1):epsilon` `"x"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(add_ebin (QuoConst a0 a1) y):epsilon` `"x"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(`(\x:epsilon. (eval (add_ebin x (y:epsilon)) to (nat))) (QuoConst a0 a1)`) THEN 
  NAT_BETA_EVAL_RED(`((\x:epsilon. (eval (x) to (nat))) (QuoConst a0 a1))`) THEN 
  NAT_BETA_EVAL_RED(`((\x:epsilon. (eval (y:epsilon) to (nat))) (QuoConst a0 a1))`)  
  );;

let y_quoconst_sub = prove( 
  `(proper_nat_construct (QuoConst a0 a1) /\
  proper_nat_construct (QuoConst b0 b1)
  ==> (\y. (eval (add_ebin (QuoConst a0 a1) y) to (nat))) (QuoConst b0 b1) =
  add_unary ((\y. (eval (QuoConst a0 a1) to (nat))) (QuoConst b0 b1))
  ((\y. (eval (y) to (nat))) (QuoConst b0 b1))) = 
  (proper_nat_construct (QuoConst a0 a1) /\
  proper_nat_construct (QuoConst b0 b1)
  ==> (eval (add_ebin (QuoConst a0 a1) (QuoConst b0 b1)) to (nat)) =
  add_unary (eval (QuoConst a0 a1) to (nat))
  (eval (QuoConst b0 b1) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [`(QuoConst a0 a1):epsilon`;`(QuoConst b0 b1):epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`(QuoConst a0 a1):epsilon`) THEN 
  PROPER_TYPE_TAC(`(QuoConst b0 b1):epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (QuoConst a0 a1) (QuoConst b0 b1)):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `(QuoConst b0 b1):epsilon` `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(QuoConst a0 a1):epsilon` `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC 
  	`(add_ebin (QuoConst a0 a1) (QuoConst b0 b1)):epsilon` `"y"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(
  	`(\y:epsilon. (eval (add_ebin (QuoConst a0 a1) (y)) to (nat))) (QuoConst b0 b1)`) THEN 
  NAT_BETA_EVAL_RED(`((\y:epsilon. (eval (QuoConst a0 a1) to (nat))) (QuoConst b0 b1))`) THEN 
  NAT_BETA_EVAL_RED(`((\y:epsilon. (eval (y) to (nat))) (QuoConst b0 b1))`)  
  );;

let y_quoapp_sub = prove( 
  `(proper_nat_construct (QuoConst a0 a1) /\
  proper_nat_construct (App b0 b1)
  ==> (\y. (eval (add_ebin (QuoConst a0 a1) y) to (nat))) (App b0 b1) =
  add_unary ((\y. (eval (QuoConst a0 a1) to (nat))) (App b0 b1))
  ((\y. (eval (y) to (nat))) (App b0 b1))) = 
  (proper_nat_construct (QuoConst a0 a1) /\
  proper_nat_construct (App b0 b1)
  ==> (eval (add_ebin (QuoConst a0 a1) (App b0 b1)) to (nat)) =
  add_unary (eval (QuoConst a0 a1) to (nat))
  (eval (App b0 b1) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [`(QuoConst a0 a1):epsilon`;`(App b0 b1):epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`(QuoConst a0 a1):epsilon`) THEN 
  PROPER_TYPE_TAC(`(App b0 b1):epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (QuoConst a0 a1) (App b0 b1)):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `(App b0 b1):epsilon` `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(QuoConst a0 a1):epsilon` `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC 
  	`(add_ebin (QuoConst a0 a1) (App b0 b1)):epsilon` `"y"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(
  	`(\y:epsilon. (eval (add_ebin (QuoConst a0 a1) (y)) to (nat))) (App b0 b1)`) THEN 
  NAT_BETA_EVAL_RED(`((\y:epsilon. (eval (QuoConst a0 a1) to (nat))) (App b0 b1))`) THEN 
  NAT_BETA_EVAL_RED(`((\y:epsilon. (eval (y) to (nat))) (App b0 b1))`)  
  );;

let x_quoapp_sub = prove(
  `(proper_nat_construct (App a0 a1)
  ==> proper_nat_construct y
  ==> (\x. (eval (add_ebin x y) to (nat))) (App a0 a1) =
  add_unary ((\x. (eval (x) to (nat))) (App a0 a1))
  ((\x. (eval (y) to (nat))) (App a0 a1))) = 
  (proper_nat_construct (App a0 a1)
  ==> proper_nat_construct y
  ==> (eval (add_ebin (App a0 a1) y) to (nat)) =
  add_unary (eval (App a0 a1) to (nat))
  (eval (y) to (nat)))`,
  REWRITE_TAC[taut_lemma] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [`(App a0 a1):epsilon`;`y:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`(App a0 a1):epsilon`) THEN 
  PROPER_TYPE_TAC(`y:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (App a0 a1) (y:epsilon)):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `(App a0 a1):epsilon` `"x"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `y:epsilon` `"x"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(add_ebin (App a0 a1) (y:epsilon)):epsilon` `"x"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(`(\x:epsilon. (eval (add_ebin (x) (y:epsilon)) to (nat))) (App a0 a1)`) THEN 
  NAT_BETA_EVAL_RED(`((\x:epsilon. (eval (x) to (nat))) (App a0 a1))`) THEN 
  NAT_BETA_EVAL_RED(`((\x:epsilon. (eval (y:epsilon) to (nat))) (App a0 a1))`)
  );;

let y_quoconst2_sub = prove( 
  `(proper_nat_construct (App a0 a1) ==>
  proper_nat_construct (QuoConst b0 b1)
  ==> (\y. (eval (add_ebin (App a0 a1) y) to (nat))) (QuoConst b0 b1) =
  add_unary ((\y. (eval (App a0 a1) to (nat))) (QuoConst b0 b1))
  ((\y. (eval (y) to (nat))) (QuoConst b0 b1))) = 
  (proper_nat_construct (App a0 a1) ==>
  proper_nat_construct (QuoConst b0 b1)
  ==> (eval (add_ebin (App a0 a1) (QuoConst b0 b1)) to (nat)) =
  add_unary (eval (App a0 a1) to (nat))
  (eval (QuoConst b0 b1) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [`(App a0 a1):epsilon`;`(QuoConst b0 b1):epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`(App a0 a1):epsilon`) THEN 
  PROPER_TYPE_TAC(`(QuoConst b0 b1):epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (App a0 a1) (QuoConst b0 b1)):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `(QuoConst b0 b1):epsilon` `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(App a0 a1):epsilon` `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC 
  	`(add_ebin (App a0 a1) (QuoConst b0 b1)):epsilon` `"y"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(
  	`(\y:epsilon. (eval (add_ebin (App a0 a1) (y)) to (nat))) (QuoConst b0 b1)`) THEN 
  NAT_BETA_EVAL_RED(`((\y:epsilon. (eval (App a0 a1) to (nat))) (QuoConst b0 b1))`) THEN 
  NAT_BETA_EVAL_RED(`((\y:epsilon. (eval (y) to (nat))) (QuoConst b0 b1))`)  
  );;

let x_case1_sub = prove( 
  `(proper_nat_construct a0 /\ proper_nat_construct y
  ==> (\x. (eval (add_ebin x y) to (nat))) a0 =
  add_unary ((\x. (eval (x) to (nat))) a0)
  ((\x. (eval (y) to (nat))) a0)) = 
  (proper_nat_construct a0 /\ proper_nat_construct y
  ==> (eval (add_ebin a0 y) to (nat)) =
  add_unary (eval a0 to (nat)) 
  (eval (y) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [`a0:epsilon`;`y:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`a0:epsilon`) THEN 
  PROPER_TYPE_TAC(`y:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin a0 y):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `a0:epsilon` `"x"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `y:epsilon` `"x"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(add_ebin (a0:epsilon) (y:epsilon)):epsilon` `"x"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(`(\x:epsilon. (eval (add_ebin x (y)) to (nat))) (a0:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`((\x:epsilon. (eval x to (nat))) (a0:epsilon))`) THEN 
  NAT_BETA_EVAL_RED(`((\x:epsilon. (eval (y:epsilon) to (nat))) (a0:epsilon))`)  
  );;

let x_case2_sub = prove( 
  `(proper_nat_construct a1 /\ proper_nat_construct y
  ==> (\x. (eval (add_ebin x y) to (nat))) a1 =
  add_unary ((\x. (eval (x) to (nat))) a1)
  ((\x. (eval (y) to (nat))) a1)) = 
  (proper_nat_construct a1 /\ proper_nat_construct y
  ==> (eval (add_ebin a1 y) to (nat)) =
  add_unary (eval a1 to (nat)) 
  (eval (y) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [`a1:epsilon`;`y:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`a1:epsilon`) THEN 
  PROPER_TYPE_TAC(`y:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin a1 y):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `a1:epsilon` `"x"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `y:epsilon` `"x"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(add_ebin (a1:epsilon) (y:epsilon)):epsilon` `"x"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(`(\x:epsilon. (eval (add_ebin x (y)) to (nat))) (a1:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`((\x:epsilon. (eval x to (nat))) (a1:epsilon))`) THEN 
  NAT_BETA_EVAL_RED(`((\x:epsilon. (eval (y:epsilon) to (nat))) (a1:epsilon))`)  
  );;

let y_case1_sub = prove(
  `(proper_nat_construct (App a0 a1)
  ==> proper_nat_construct b0
  ==> (\y:epsilon. (eval (add_ebin (App a0 a1) y) to (nat))) b0 =
  add_unary ((\y:epsilon. (eval (App a0 a1) to (nat))) b0)
  ((\y:epsilon. (eval (y) to (nat))) b0)) = 
  (proper_nat_construct (App a0 a1) /\ proper_nat_construct b0
  ==> (eval (add_ebin (App a0 a1) b0) to (nat)) =
  add_unary (eval (App a0 a1) to (nat)) 
  (eval (b0:epsilon) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [`(App a0 a1):epsilon`;`b0:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`(App a0 a1):epsilon`) THEN 
  PROPER_TYPE_TAC(`b0:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (App a0 a1) b0):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `(App a0 a1):epsilon` `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `b0:epsilon` `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC 
  	`(add_ebin ((App a0 a1):epsilon) (b0:epsilon)):epsilon` `"y"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(`(\y:epsilon. (eval (add_ebin (App a0 a1) (y)) to (nat))) (b0:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`((\y:epsilon. (eval (App a0 a1) to (nat))) (b0:epsilon))`) THEN 
  NAT_BETA_EVAL_RED(`((\y:epsilon. (eval (y:epsilon) to (nat))) (b0:epsilon))`)  
  );;

let y_case2_sub = prove(
  `(proper_nat_construct (App a0 a1)
  ==> proper_nat_construct b1
  ==> (\y:epsilon. (eval (add_ebin (App a0 a1) y) to (nat))) b1 =
  add_unary ((\y:epsilon. (eval (App a0 a1) to (nat))) b1)
  ((\y:epsilon. (eval (y) to (nat))) b1)) = 
  (proper_nat_construct (App a0 a1) /\ proper_nat_construct b1
  ==> (eval (add_ebin (App a0 a1) b1) to (nat)) =
  add_unary (eval (App a0 a1) to (nat)) 
  (eval (b1:epsilon) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [`(App a0 a1):epsilon`;`b1:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`(App a0 a1):epsilon`) THEN 
  PROPER_TYPE_TAC(`b1:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (App a0 a1) b1):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `(App a0 a1):epsilon` `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `b1:epsilon` `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC 
  	`(add_ebin ((App a0 a1):epsilon) (b1:epsilon)):epsilon` `"y"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(`(\y:epsilon. (eval (add_ebin (App a0 a1) (y)) to (nat))) (b1:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`((\y:epsilon. (eval (App a0 a1) to (nat))) (b1:epsilon))`) THEN 
  NAT_BETA_EVAL_RED(`((\y:epsilon. (eval (y:epsilon) to (nat))) (b1:epsilon))`)  
  );;

let y_quoapp_app_sub = prove(
  `(proper_nat_construct (App a0 a1)
  ==> proper_nat_construct (App b0 b1)
  ==> (\y:epsilon. (eval (add_ebin (App a0 a1) y) to (nat))) (App b0 b1) =
  add_unary ((\y:epsilon. (eval (App a0 a1) to (nat))) (App b0 b1))
  ((\y:epsilon. (eval (y) to (nat))) (App b0 b1))) = 
  (proper_nat_construct (App a0 a1) /\ proper_nat_construct (App b0 b1)
  ==> (eval (add_ebin (App a0 a1) (App b0 b1)) to (nat)) =
  add_unary (eval (App a0 a1) to (nat)) 
  (eval ((App b0 b1):epsilon) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [`(App a0 a1):epsilon`;`(App b0 b1):epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`(App a0 a1):epsilon`) THEN 
  PROPER_TYPE_TAC(`(App b0 b1):epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (App a0 a1) (App b0 b1)):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `(App a0 a1):epsilon` `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(App b0 b1):epsilon` `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC 
  	`(add_ebin ((App a0 a1):epsilon) ((App b0 b1):epsilon)):epsilon` `"y"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(
  	`(\y:epsilon. (eval (add_ebin (App a0 a1) (y)) to (nat))) ((App b0 b1):epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`((\y:epsilon. (eval (App a0 a1) to (nat))) ((App b0 b1):epsilon))`) THEN 
  NAT_BETA_EVAL_RED(`((\y:epsilon. (eval (y:epsilon) to (nat))) ((App b0 b1):epsilon))`)  
  );;

let y_quoapp_case1_sub = prove(
  `(proper_nat_construct (a1:epsilon)
  ==> proper_nat_construct (b1:epsilon)
  ==> (\y:epsilon. (eval (add_ebin a1 y) to (nat))) b1 =
  add_unary ((\y:epsilon. (eval (a1) to (nat))) b1)
  ((\y:epsilon. (eval (y) to (nat))) b1)) = 
  (proper_nat_construct (a1:epsilon)
  ==> proper_nat_construct (b1:epsilon)
  ==> (eval (add_ebin a1 b1) to (nat)) =
  add_unary (eval (a1) to (nat))
  (eval (b1) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [`a1:epsilon`;`b1:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`a1:epsilon`) THEN 
  PROPER_TYPE_TAC(`b1:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin a1 b1):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `a1:epsilon` `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `b1:epsilon` `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(add_ebin (a1:epsilon) (b1:epsilon)):epsilon` `"y"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(`(\y:epsilon. (eval (add_ebin a1 (y)) to (nat))) (b1:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`((\y:epsilon. (eval (a1:epsilon) to (nat))) (b1:epsilon))`) THEN 
  NAT_BETA_EVAL_RED(`((\y:epsilon. (eval (y:epsilon) to (nat))) (b1:epsilon))`)  
   );;

let fin_x_sub = prove(
  `proper_nat_construct (add_ebin a1 b1) ==> 
  ((\x. (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)))
  (add_ebin a1 b1) =
  add_unary One ((\x. (eval (x) to (nat))) (add_ebin a1 b1))) = 
  ((eval (add_ebin (QuoConst "One" (TyBase "nat")) (add_ebin a1 b1)) to (nat)) =
  add_unary One (eval (add_ebin a1 b1) to (nat)))`,
  DISCH_TAC THEN 
  SUBGOAL_THEN `proper_nat_construct (QuoConst "One" (TyBase "nat"))` ASSUME_TAC THEN 
  REWRITE_TAC[proper_nat_construct] THEN 
  MP_TAC(SPECL [
  	`(QuoConst "One" (TyBase "nat")):epsilon`;`(add_ebin a1 b1):epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`(QuoConst "One" (TyBase "nat")):epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin a1 b1):epsilon`) THEN 
  PROPER_TYPE_TAC(
  	`(add_ebin (QuoConst "One" (TyBase "nat")) (add_ebin a1 b1)):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `(add_ebin a1 b1):epsilon` `"x"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC 
  	`(add_ebin (QuoConst "One" (TyBase "nat")) (add_ebin a1 b1)):epsilon` 
  	`"x"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(
  	`(\x:epsilon. (eval (add_ebin (QuoConst "One" (TyBase "nat")) (x)) to (nat))) 
  	(add_ebin a1 b1)`) THEN 
  NAT_BETA_EVAL_RED(`((\x:epsilon. (eval (x:epsilon) to (nat))) (add_ebin a1 b1))`)
  );;


(* Final theroem needed *)
let ind_3 = NOT_FREE_ABS_NOT_EFFECTIVE_CONV `x:epsilon` 
  `proper_nat_construct x ==> 
  eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat) = 
  add_unary One (eval x to (nat))` `w:epsilon`;;
addNotEff ind_3;;

let x_thm3_sub = prove( 
  `(proper_nat_construct x
  ==> (\a0:string. (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat))) (w:string) =
  add_unary One ((\a0:string. (eval (x) to (nat))) (w:string))) = 
  (proper_nat_construct x
  ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)) =
  add_unary One (eval (x) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [`(QuoConst "One" (TyBase "nat")):epsilon`;`x:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[proper_nat_construct] THEN 
  DISCH_TAC THEN 
  SUBGOAL_THEN `proper_nat_construct (QuoConst "One" (TyBase "nat"))` ASSUME_TAC THEN 
  REWRITE_TAC[proper_nat_construct] THEN 
  PROPER_TYPE_TAC(`(QuoConst "One" (TyBase "nat")):epsilon`) THEN 
  PROPER_TYPE_TAC(`x:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (QuoConst "One" (TyBase "nat")) x):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC 
  	`(QuoConst "One" (TyBase "nat")):epsilon` `"a0"` `TyMonoCons "list" (TyBase "char")`) THEN 
  (PROPER_NOT_FREE_TAC `(x):epsilon` `"a0"` `TyMonoCons "list" (TyBase "char")`) THEN 
  (PROPER_NOT_FREE_TAC 
  	`(add_ebin (QuoConst "One" (TyBase "nat")) x):epsilon` `"a0"` 
  	`TyMonoCons "list" (TyBase "char")`) THEN 
  NAT_BETA_EVAL_RED(
  	`(\a0:string. 
  	(eval (add_ebin (QuoConst "One" (TyBase "nat")) (x:epsilon)) to (nat))) (w:string)`) THEN 
  NAT_BETA_EVAL_RED(
  	`((\a0:string. (eval (QuoConst "One" (TyBase "nat")) to (nat))) (w:string))`) THEN 
  NAT_BETA_EVAL_RED(`((\a0:string. (eval (x:epsilon) to (nat))) (w:string))`)  
  );;

let a0_ne_thm3 = prove(
  mk_not_effective_in `a0:string` 
  `\x. proper_nat_construct x
  ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)) =
  add_unary One (eval (x) to (nat))` `w:string`,
  GEN_TAC THEN 
  REWRITE_TAC[BETA_RED_BY_SUB `(\a0:string. \x. proper_nat_construct x
    ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)) =
    add_unary One (eval (x) to (nat))) (w:string)`] THEN 
  REWRITE_TAC[x_thm3_sub]
  );;
addNotEff a0_ne_thm3;;

let a1_thm3_sub = prove( 
  `(proper_nat_construct x
  ==> (\a1:type. (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat))) (w:type) =
  add_unary One ((\a1:type. (eval (x) to (nat))) (w:type))) = 
  (proper_nat_construct x
  ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)) =
  add_unary One (eval (x) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [`(QuoConst "One" (TyBase "nat")):epsilon`;`x:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[proper_nat_construct] THEN 
  DISCH_TAC THEN 
  SUBGOAL_THEN `proper_nat_construct (QuoConst "One" (TyBase "nat"))` ASSUME_TAC THEN 
  REWRITE_TAC[proper_nat_construct] THEN 
  PROPER_TYPE_TAC(`(QuoConst "One" (TyBase "nat")):epsilon`) THEN 
  PROPER_TYPE_TAC(`x:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (QuoConst "One" (TyBase "nat")) x):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC 
  	`(QuoConst "One" (TyBase "nat")):epsilon` `"a1"` `TyBase "type"`) THEN 
  (PROPER_NOT_FREE_TAC `(x):epsilon` `"a1"` `TyBase "type"`) THEN 
  (PROPER_NOT_FREE_TAC 
  	`(add_ebin (QuoConst "One" (TyBase "nat")) x):epsilon` `"a1"` `TyBase "type"`) THEN 
  NAT_BETA_EVAL_RED(
  	`(\a1:type. 
  	(eval (add_ebin (QuoConst "One" (TyBase "nat")) (x:epsilon)) to (nat))) (w:type)`) THEN 
  NAT_BETA_EVAL_RED(
  	`((\a1:type. (eval (QuoConst "One" (TyBase "nat")) to (nat))) (w:type))`) THEN 
  NAT_BETA_EVAL_RED(`((\a1:type. (eval (x:epsilon) to (nat))) (w:type))`)  
  );;

let a1_ne_thm3 = prove(
  mk_not_effective_in `a1:type` 
  `\x. proper_nat_construct x
  ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)) =
  add_unary One (eval (x) to (nat))` `w:type`,
  GEN_TAC THEN 
  REWRITE_TAC[BETA_RED_BY_SUB `(\a1:type. \x. proper_nat_construct x
    ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)) =
    add_unary One (eval (x) to (nat))) (w:type)`] THEN 
  REWRITE_TAC[a1_thm3_sub]
  );;
addNotEff a1_ne_thm3;;

let thm3_x_quoconst = prove(
  `(proper_nat_construct (QuoConst a0 a1)
  ==> (\x. (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)))
  (QuoConst a0 a1) =
  add_unary One ((\x. (eval (x) to (nat))) (QuoConst a0 a1))) = 
  (proper_nat_construct (QuoConst a0 a1)
  ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) (QuoConst a0 a1)) to (nat)) =
  add_unary One (eval (QuoConst a0 a1) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [
    `(QuoConst "One" (TyBase "nat")):epsilon`;
    `(QuoConst a0 a1):epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[proper_nat_construct] THEN 
  DISCH_TAC THEN 
  SUBGOAL_THEN `proper_nat_construct (QuoConst "One" (TyBase "nat"))` ASSUME_TAC THEN 
  REWRITE_TAC[proper_nat_construct] THEN 
  PROPER_TYPE_TAC(`(QuoConst "One" (TyBase "nat")):epsilon`) THEN 
  PROPER_TYPE_TAC(`(QuoConst a0 a1):epsilon`) THEN 
  PROPER_TYPE_TAC(
    `(add_ebin (QuoConst "One" (TyBase "nat")) (QuoConst a0 a1)):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `(QuoConst a0 a1):epsilon` `"x"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC 
    `(add_ebin (QuoConst "One" (TyBase "nat")) 
    (QuoConst a0 a1)):epsilon` `"x"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(
    `(\x:epsilon. (eval (add_ebin (QuoConst "One" (TyBase "nat")) 
    (x:epsilon)) to (nat))) (QuoConst a0 a1)`) THEN 
  NAT_BETA_EVAL_RED(`((\x:epsilon. (eval (x:epsilon) to (nat))) (QuoConst a0 a1))`)  
  );;

let x_eps_thm3_sub = prove( 
  `(proper_nat_construct x ==> 
  (\a0:epsilon. (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat))) (w:epsilon) =
  add_unary One ((\a0:epsilon. (eval (x) to (nat))) (w:epsilon))) = 
  (proper_nat_construct x ==> 
  (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)) =
  add_unary One (eval (x) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [`(QuoConst "One" (TyBase "nat")):epsilon`;`x:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[proper_nat_construct] THEN 
  DISCH_TAC THEN 
  SUBGOAL_THEN `proper_nat_construct (QuoConst "One" (TyBase "nat"))` ASSUME_TAC THEN 
  REWRITE_TAC[proper_nat_construct] THEN 
  PROPER_TYPE_TAC(`(QuoConst "One" (TyBase "nat")):epsilon`) THEN 
  PROPER_TYPE_TAC(`x:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (QuoConst "One" (TyBase "nat")) x):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC 
    `(QuoConst "One" (TyBase "nat")):epsilon` `"a0"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC `(x):epsilon` `"a0"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC 
    `(add_ebin (QuoConst "One" (TyBase "nat")) x):epsilon` `"a0"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(
    `(\a0:epsilon. (eval (add_ebin (QuoConst "One" (TyBase "nat")) 
    (x:epsilon)) to (nat))) (w:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(
    `((\a0:epsilon. (eval (QuoConst "One" (TyBase "nat")) to (nat))) (w:epsilon))`) THEN 
  NAT_BETA_EVAL_RED(`((\a0:epsilon. (eval (x:epsilon) to (nat))) (w:epsilon))`)  
  );;

let a0_eps_ne_thm3 = prove(
  mk_not_effective_in `a0:epsilon` 
  `\x. proper_nat_construct x
  ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)) =
  add_unary One (eval (x) to (nat))` `w:epsilon`,
  GEN_TAC THEN 
  REWRITE_TAC[BETA_RED_BY_SUB `(\a0:epsilon. \x. proper_nat_construct x
    ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)) =
    add_unary One (eval (x) to (nat))) (w:epsilon)`] THEN 
  REWRITE_TAC[x_eps_thm3_sub]
  );;
addNotEff a0_eps_ne_thm3;;

let a1_eps_ne_thm3 = 
  let tm = (mk_not_effective_in `a1:epsilon` 
    `\x. proper_nat_construct x
    ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)) =
    add_unary One (eval (x) to (nat))` `w:epsilon`) 
  in
  EQ_MP (ALPHA (concl a0_eps_ne_thm3) tm) a0_eps_ne_thm3;;
addNotEff a1_eps_ne_thm3;;

let a_eps_ne_thm3 = 
  let tm = (mk_not_effective_in `a:epsilon` 
    `\x. proper_nat_construct x
    ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)) =
    add_unary One (eval (x) to (nat))` `w:epsilon`) 
  in
  EQ_MP (ALPHA (concl a0_eps_ne_thm3) tm) a0_eps_ne_thm3;;
addNotEff a_eps_ne_thm3;;

let sub_a1_thm = prove(
  `(proper_nat_construct a1
  ==> (\x:epsilon. 
  (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat))) a1 =
  add_unary One ((\x:epsilon. (eval (x) to (nat))) a1)) = 
  (proper_nat_construct a1
  ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) a1) to (nat)) =
  add_unary One (eval (a1:epsilon) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN 
    `proper_nat_construct (QuoConst "One" (TyBase "nat"))` ASSUME_TAC THEN 
  REWRITE_TAC[proper_nat_construct] THEN  
  MP_TAC(SPECL [
    `(QuoConst "One" (TyBase "nat")):epsilon`;`a1:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`(QuoConst "One" (TyBase "nat")):epsilon`) THEN 
  PROPER_TYPE_TAC(`a1:epsilon`) THEN 
  PROPER_TYPE_TAC(`(add_ebin (QuoConst "One" (TyBase "nat")) a1):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `a1:epsilon` `"x"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC 
    `(add_ebin ((QuoConst "One" (TyBase "nat")):epsilon) 
    (a1:epsilon)):epsilon` `"x"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(
    `(\x:epsilon. (eval (add_ebin (QuoConst "One" (TyBase "nat")) 
    (x:epsilon)) to (nat))) (a1:epsilon)`) THEN 
  NAT_BETA_EVAL_RED(`((\x:epsilon. (eval (x:epsilon) to (nat))) (a1:epsilon))`) 
  );;

let sub_app_thm = prove(
  `(proper_nat_construct (App a0 a1)
  ==> (\x:epsilon. 
  (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat))) (App a0 a1) =
  add_unary One ((\x:epsilon. (eval (x) to (nat))) (App a0 a1))) = 
  (proper_nat_construct (App a0 a1)
  ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) (App a0 a1)) to (nat)) =
  add_unary One (eval (App a0 a1) to (nat)))`,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN 
    `proper_nat_construct (QuoConst "One" (TyBase "nat"))` ASSUME_TAC THEN 
  REWRITE_TAC[proper_nat_construct] THEN  
  MP_TAC(SPECL [
    `(QuoConst "One" (TyBase "nat")):epsilon`;`(App a0 a1):epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`(QuoConst "One" (TyBase "nat")):epsilon`) THEN 
  PROPER_TYPE_TAC(`(App a0 a1):epsilon`) THEN 
  PROPER_TYPE_TAC(
    `(add_ebin (QuoConst "One" (TyBase "nat")) (App a0 a1)):epsilon`) THEN 
  (PROPER_NOT_FREE_TAC `(App a0 a1):epsilon` `"x"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC 
    `(add_ebin ((QuoConst "One" (TyBase "nat")):epsilon) 
    ((App a0 a1):epsilon)):epsilon` `"x"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(
    `(\x:epsilon. (eval (add_ebin (QuoConst "One" (TyBase "nat")) 
    (x:epsilon)) to (nat))) (App a0 a1)`) THEN 
  NAT_BETA_EVAL_RED(`((\x:epsilon. (eval (x:epsilon) to (nat))) (App a0 a1))`) 
  );;

let thm3 = prove(
  `!x:epsilon. proper_nat_construct x ==> 
  eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat) = 
  add_unary One (eval x to (nat))`,
  MATCH_MP_TAC(lth) THEN 
  CONJ_TAC THENL
  [REWRITE_TAC[proper_nat_construct]
  ;CONJ_TAC THENL
  [REPEAT GEN_TAC THEN 
  REWRITE_TAC[thm3_x_quoconst] THEN 
  REWRITE_TAC[proper_nat_construct;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  DISJ_CASES_TAC(ASSUME `a0 = "Zero" \/ a0 = "One"`) THEN 
  ASM_REWRITE_TAC[add_ebin] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[add_unary;thenZero;one_def]
  ;CONJ_TAC THENL
  [REPEAT GEN_TAC THEN 
  REWRITE_TAC[sub_a1_thm;sub_app_thm;IMP_CONJ] THEN 
  DISCH_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[proper_nat_construct;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  DISJ_CASES_TAC(ASSUME 
    `(a0 = QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
    a0 = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))`) THEN 
  ASM_REWRITE_TAC[add_ebin] THENL
  [MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  PROPER_TYPE_TAC(`a1:epsilon`) THEN 
  ASM_REWRITE_TAC[] THEN 
  IS_EXPR_TYPE_TAC THEN
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[one_def;take_s;id_of_plus;add_one_even]
  ;MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `(add_ebin (QuoConst "One" (TyBase "nat")) a1):epsilon`) THEN 
  PROPER_TYPE_TAC(`a1:epsilon`) THEN
  SUBGOAL_THEN 
    `proper_nat_construct (QuoConst "One" (TyBase "nat"))` ASSUME_TAC THEN 
  REWRITE_TAC[proper_nat_construct] THEN 
  MP_TAC(SPECL [`(QuoConst "One" (TyBase "nat"))`;`a1:epsilon`] thm1) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  IS_EXPR_TYPE_TAC THEN
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[one_def;take_s;id_of_plus;add_one_even] THEN 
  MP_TAC(ASSUME `proper_nat_construct a1
  ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) a1) to (nat)) =
  add_unary One (eval (a1) to (nat))`) THEN 
  REWRITE_TAC[ASSUME `proper_nat_construct a1`] THEN 
  DISCH_TAC THEN 
  QUOTE_TO_CONSTRUCTION_TAC THEN
  ASM_REWRITE_TAC[
    carry_one;one_def;take_s;id_of_plus;add_one_even;take_out_S;odd_to_even]
  ]
  ;REWRITE_TAC[proper_nat_construct]
  ]
  ]
  ]
  );;



(*                                                     *)
(* Meaning formula for addition                        *)
(*                                                     *)

let add_meaning = 
  let tm = 
    `(!x:epsilon y:epsilon. 
    (((proper_nat_construct x) /\ (proper_nat_construct y)) 
    ==> (eval (add_ebin x y) to (nat) =  
    add_unary (eval x to (nat)) (eval y to (nat)))))` 
  in 
  prove(tm, 
  MATCH_MP_TAC(lth) THEN 
  CONJ_TAC THENL
  [(* isVar x *)
  REWRITE_TAC[proper_nat_construct]
  ;CONJ_TAC THENL
  [(* isConst x  *)
  GEN_TAC THEN 
  GEN_TAC THEN 
  REWRITE_TAC[x_quoconst_sub] THEN 
  MATCH_MP_TAC(eps_alt_ind) THEN 
  CONJ_TAC THENL
  [(* isVar y  *)
  REWRITE_TAC[proper_nat_construct]
  ;CONJ_TAC THENL
  [(* isConst y *)
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[y_quoconst_sub;proper_nat_construct;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  DISJ_CASES_TAC(ASSUME `a0 = "Zero" \/ a0 = "One"`) THEN 
  DISJ_CASES_TAC(ASSUME `b0 = "Zero" \/ b0 = "One"`) THEN 
  ASM_REWRITE_TAC[add_ebin] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[one_def;add_unary;thenZero]
  ;CONJ_TAC THENL
  [(* isApp y *) 
  REPEAT GEN_TAC THEN
  REWRITE_TAC[y_quoapp_sub;proper_nat_construct;IMP_CONJ] THEN
  REPEAT DISCH_TAC THEN 
  DISJ_CASES_TAC(ASSUME `a0 = "Zero" \/ a0 = "One"`) THENL
  [ASM_REWRITE_TAC[add_ebin] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[id_of_plus]
  ;DISJ_CASES_TAC(ASSUME 
    `b0 = QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
    b0 = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THEN 
  ASM_REWRITE_TAC[add_ebin] THENL
  [MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `b1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `b1:epsilon`) THEN
  PROPER_TYPE_TAC(`b1:epsilon`) THEN
  IS_EXPR_TYPE_TAC THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN
  REWRITE_TAC[remove_one]
  ;MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `b1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `(add_ebin (QuoConst "One" (TyBase "nat")) b1):epsilon`) THEN
  MP_TAC(SPECL [`(QuoConst "One" (TyBase "nat"))`;`b1:epsilon`] thm1) THEN
  REWRITE_TAC[
    proper_nat_construct;
    ASSUME `proper_nat_construct (b1:epsilon)`] THEN
  DISCH_TAC THEN  
  ASM_REWRITE_TAC[] THEN
  PROPER_TYPE_TAC(`b1:epsilon`) THEN
  IS_EXPR_TYPE_TAC THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  MP_TAC(SPECL [`(QuoConst "One" (TyBase "nat"))`;`b1:epsilon`] lemma6) THEN 
  REWRITE_TAC[
    ASSUME `proper_nat_construct (b1:epsilon)`;
    proper_nat_construct] THEN 
  DISCH_TAC THEN 
  MP_TAC(ASSUME `a0 = "Zero" \/ a0 = "One"
    ==> a1 = TyBase "nat"
    ==> proper_nat_construct b1
    ==> (\y. (eval (add_ebin (QuoConst a0 a1) y) to (nat))) b1 =
    add_unary ((\y. (eval (QuoConst a0 a1) to (nat))) b1)
    ((\y. (eval (y) to (nat))) b1)`) THEN 
  REWRITE_TAC[
    ASSUME `a0 = "One"`; 
    ASSUME `a1 = TyBase "nat"`; 
    ASSUME `proper_nat_construct b1`] THEN 
  (PROPER_NOT_FREE_TAC 
    `(add_ebin (QuoConst "One" (TyBase "nat")) b1):epsilon` 
    `"y":string` `(TyBase "epsilon"):type`) THEN 
  NAT_BETA_EVAL_RED(
    `(\y. (eval (add_ebin (QuoConst "One" (TyBase "nat")) y) to (nat))) b1`) THEN 
  (PROPER_NOT_FREE_TAC 
    `(QuoConst "One" (TyBase "nat"))` 
    `"y":string` `(TyBase "epsilon"):type`) THEN 
  MP_TAC(IS_EXPR_TYPE_CONV `One:nat`) THEN 
  DISCH_TAC THEN 
  NAT_BETA_EVAL_RED(
    `(\y:epsilon. (eval (QuoConst "One" (TyBase "nat")) to (nat))) b1`) THEN 
  (PROPER_NOT_FREE_TAC `b1:epsilon` `"y":string` `(TyBase "epsilon"):type`) THEN 
  NAT_BETA_EVAL_RED(`(\y:epsilon. (eval (y) to (nat))) b1`) THEN 
  DISCH_TAC THEN 
  QUOTE_TO_CONSTRUCTION_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN
  REWRITE_TAC[carry_one]
  ]
  ]
  ;REWRITE_TAC[proper_nat_construct]
  ]
  ]
  ]
  ;CONJ_TAC THENL
  [(* isApp x *)
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[IMP_CONJ;x_case1_sub;x_case2_sub;x_quoapp_sub] THEN 
  REPEAT DISCH_TAC THEN 
  MATCH_MP_TAC(eps_alt_ind) THEN 
  CONJ_TAC THENL
  [(* isVar y *)
  REWRITE_TAC[proper_nat_construct]
  ;CONJ_TAC THENL
  [(* isConst y *)
  REPEAT GEN_TAC THEN
  REWRITE_TAC[y_quoconst2_sub;proper_nat_construct] THEN
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  DISJ_CASES_TAC(ASSUME `(b0 = "Zero" \/ b0 = "One")`) THENL
  [ASM_REWRITE_TAC[add_ebin] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[add_unary]
  ;DISJ_CASES_TAC(ASSUME 
    `a0 = QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
    a0 = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THEN 
  ASM_REWRITE_TAC[add_ebin] THENL
  [MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`  
    `a1:epsilon`) THEN
  PROPER_TYPE_TAC(`a1:epsilon`) THEN
  IS_EXPR_TYPE_TAC THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN
  REWRITE_TAC[sym_add;remove_one]
  ;MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `(add_ebin (QuoConst "One" (TyBase "nat")) a1):epsilon`) THEN
  MP_TAC(SPECL [`a1:epsilon`;`(QuoConst "One" (TyBase "nat"))`] thm1) THEN
  MP_TAC(SPECL [`(QuoConst "One" (TyBase "nat"))`;`a1:epsilon`] thm1) THEN 
  REWRITE_TAC[
    ASSUME `proper_nat_construct (a1:epsilon)`;
    proper_nat_construct] THEN
  DISCH_TAC THEN  
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN
  PROPER_TYPE_TAC(`a1:epsilon`) THEN
  IS_EXPR_TYPE_TAC THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  MP_TAC(SPEC `QuoConst "One" (TyBase "nat")` (ASSUME 
    `!y. proper_nat_construct a1
    ==> proper_nat_construct y
    ==> (eval (add_ebin a1 y) to (nat)) =
    add_unary (eval (a1) to (nat)) (eval (y) to (nat))`)) THEN 
  MP_TAC(SPECL [`a1:epsilon`;`(QuoConst "One" (TyBase "nat"))`] lemma6) THEN 
  REWRITE_TAC[ 
    ASSUME `proper_nat_construct (a1:epsilon)`;
    proper_nat_construct] THEN 
  DISCH_TAC THEN 
  (PROPER_NOT_FREE_TAC 
    `(add_ebin a1 (QuoConst "One" (TyBase "nat"))):epsilon` 
    `"y":string` `(TyBase "epsilon"):type`) THEN 
  NAT_BETA_EVAL_RED(
    `(\y:epsilon. (eval (add_ebin (a1:epsilon) y) to (nat))) 
    (QuoConst "One" (TyBase "nat"))`) THEN 
  (PROPER_NOT_FREE_TAC `a1:epsilon` `"y":string` `(TyBase "epsilon"):type`) THEN 
  NAT_BETA_EVAL_RED(
    `(\y:epsilon. (eval 
    (a1:epsilon) to (nat))) (QuoConst "One" (TyBase "nat"))`) THEN 
  (PROPER_NOT_FREE_TAC 
    `QuoConst "One" (TyBase "nat")` `"y":string` `(TyBase "epsilon"):type`) THEN 
  NAT_BETA_EVAL_RED(
    `(\y:epsilon. (eval (y) to (nat))) (QuoConst "One" (TyBase "nat"))`) THEN 
  IS_EXPR_TYPE_TAC THEN 
  DISCH_TAC THEN 
  QUOTE_TO_CONSTRUCTION_TAC THEN 
  MP_TAC(
    SPECL [`(QuoConst "One" (TyBase "nat"))`;`a1:epsilon`] ebin_sym_add) THEN 
  REWRITE_TAC[
    ASSUME `proper_nat_construct (a1:epsilon)`;
    proper_nat_construct] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[sym_add] THEN 
  REWRITE_TAC[carry_one]
  ]
  ]
  ;CONJ_TAC THENL
  [(* isApp y *)
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[y_case1_sub;y_case2_sub;y_quoapp_app_sub;IMP_CONJ] THEN
  DISCH_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[proper_nat_construct] THEN 
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  DISJ_CASES_TAC(ASSUME 
    `a0 = QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
    a0 = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THEN 
  DISJ_CASES_TAC(ASSUME 
    `b0 = QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")) \/
    b0 = QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`) THEN
  ASM_REWRITE_TAC[add_ebin] THENL
  [MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `(add_ebin a1 b1):epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `b1:epsilon`) THEN 
  PROPER_TYPE_TAC(`a1:epsilon`) THEN 
  PROPER_TYPE_TAC(`b1:epsilon`) THEN 
  MP_TAC(SPECL [`a1:epsilon`;`b1:epsilon`] thm1) THEN 
  REWRITE_TAC[
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  IS_EXPR_TYPE_TAC THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN
  CONSTRUCTION_TO_QUOTE_TAC THEN
  LAW_OF_DISQUO_TAC THEN 
  MP_TAC(SPEC `b1:epsilon` (ASSUME `!y. proper_nat_construct a1
  ==> proper_nat_construct y
  ==> (eval (add_ebin a1 y) to (nat)) =
  add_unary (eval (a1) to (nat)) (eval (y) to (nat))`)) THEN 
  REWRITE_TAC[
    y_quoapp_case1_sub;
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[add_even]
  ;MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `b1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `(add_ebin a1 b1):epsilon`) THEN 
  PROPER_TYPE_TAC(`a1:epsilon`) THEN 
  PROPER_TYPE_TAC(`b1:epsilon`) THEN 
  MP_TAC(SPECL [`a1:epsilon`;`b1:epsilon`] thm1) THEN 
  REWRITE_TAC[
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  IS_EXPR_TYPE_TAC THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN
  CONSTRUCTION_TO_QUOTE_TAC THEN
  LAW_OF_DISQUO_TAC THEN 
  MP_TAC(SPEC `b1:epsilon` (ASSUME 
    `!y. proper_nat_construct a1
    ==> proper_nat_construct y
    ==> (eval (add_ebin a1 y) to (nat)) =
    add_unary (eval (a1) to (nat)) (eval (y) to (nat))`)) THEN 
  REWRITE_TAC[
    y_quoapp_case1_sub;
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[add_even_odd]
  ;MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `b1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `(add_ebin a1 b1):epsilon`) THEN 
  PROPER_TYPE_TAC(`a1:epsilon`) THEN 
  PROPER_TYPE_TAC(`b1:epsilon`) THEN 
  MP_TAC(SPECL [`a1:epsilon`;`b1:epsilon`] thm1) THEN 
  REWRITE_TAC[
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  IS_EXPR_TYPE_TAC THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN
  CONSTRUCTION_TO_QUOTE_TAC THEN
  LAW_OF_DISQUO_TAC THEN 
  MP_TAC(SPEC `b1:epsilon` (ASSUME 
    `!y. proper_nat_construct a1
    ==> proper_nat_construct y
    ==> (eval (add_ebin a1 y) to (nat)) =
    add_unary (eval (a1) to (nat)) (eval (y) to (nat))`)) THEN 
  REWRITE_TAC[
    y_quoapp_case1_sub;
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[add_odd_even]
  ;MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `b1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `(add_ebin (QuoConst "One" (TyBase "nat")) (add_ebin a1 b1)):epsilon`) THEN 
  PROPER_TYPE_TAC(`a1:epsilon`) THEN 
  PROPER_TYPE_TAC(`b1:epsilon`) THEN 
  MP_TAC(SPECL [`a1:epsilon`;`b1:epsilon`] thm1) THEN 
  REWRITE_TAC[
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`a1:epsilon`;`b1:epsilon`] lemma6) THEN  
  REWRITE_TAC[
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN 
  DISCH_TAC THEN 
  MP_TAC(SPECL [
    `(QuoConst "One" (TyBase "nat")):epsilon`;
    `(add_ebin a1 b1):epsilon`] thm1) THEN 
  REWRITE_TAC[
    ASSUME `proper_nat_construct (add_ebin a1 b1)`;
    proper_nat_construct] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  IS_EXPR_TYPE_TAC THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN
  CONSTRUCTION_TO_QUOTE_TAC THEN
  LAW_OF_DISQUO_TAC THEN  
  ASM_REWRITE_TAC[add_odd_even] THEN 
  QUOTE_TO_CONSTRUCTION_TAC THEN 
  MP_TAC(SPEC `(add_ebin a1 b1)` thm3) THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_TAC(fin_x_sub) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_TAC(SPEC `b1:epsilon` (ASSUME 
    `!y. proper_nat_construct a1
    ==> proper_nat_construct y
    ==> (eval (add_ebin a1 y) to (nat)) =
    add_unary (eval (a1) to (nat)) (eval (y) to (nat))`)) THEN 
  REWRITE_TAC[
    y_quoapp_case1_sub;
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_TAC(SYM(SPEC 
    `add_unary (eval (a1:epsilon) to (nat)) (eval (b1:epsilon) to (nat))` 
    carry_one)) THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  REWRITE_TAC[add_even_odd;one_def;take_s;id_of_plus] THEN
  REWRITE_TAC[put_s;add_one_even] 
  ]
  ;REWRITE_TAC[proper_nat_construct]
  ]
  ]
  ]
  ;REWRITE_TAC[proper_nat_construct]
  ]
  ]
  ]
  );;



