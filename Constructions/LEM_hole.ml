needs "Constructions/QuotationTactics.ml";;

	(* Alternative LEM formula (with holes) *)


let holed_lem = 
	prove(`!x:epsilon. (isExprType x (TyBase "bool") ==> 
			((eval Q_ H_ x _H of bool \/ ~ (H_ x _H of bool) _Q to bool)))`,
		GEN_TAC THEN 
		QUOTE_TO_CONSTRUCTION_TAC THEN
		REWRITE_TAC[isExprType] THEN 
		REWRITE_TAC[IMP_CONJ] THEN
		REPEAT(DISCH_TAC) THEN 
		MP_TAC(APP_DISQUO 
			`App (QuoConst "\\/" (TyBiCons "fun" (TyBase "bool") (TyBiCons "fun" (TyBase "bool") (TyBase "bool"))))(x:epsilon)`
			`App (QuoConst "~" (TyBiCons "fun" (TyBase "bool") (TyBase "bool"))) (x:epsilon)`) THEN
		IS_EXPR_TYPE_TAC THEN 
		DISCH_TAC THEN
		ASM_REWRITE_TAC[] THEN
		MP_TAC(APP_DISQUO `QuoConst "\\/" (TyBiCons "fun" (TyBase "bool") (TyBiCons "fun" (TyBase "bool") (TyBase "bool")))` `x:epsilon`) THEN
		IS_EXPR_TYPE_TAC THEN 
		DISCH_TAC THEN
		ASM_REWRITE_TAC[] THEN 
		MP_TAC(APP_DISQUO `QuoConst "~" (TyBiCons "fun" (TyBase "bool") (TyBase "bool"))` `x:epsilon`) THEN
		IS_EXPR_TYPE_TAC THEN 
		DISCH_TAC THEN
		ASM_REWRITE_TAC[] THEN 
		CONSTRUCTION_TO_QUOTE_TAC THEN 
		LAW_OF_DISQUO_TAC THEN 
		REWRITE_TAC[EXCLUDED_MIDDLE]);;


let stmt = termToConstruction `?n:num. !m:num. n > m`;;

(* Proof by instantiating holed_lem *)
let hole_LEM_ex = 
	prove(`(?n:num. !m:num. n > m) \/ ~ (?n:num. !m:num. n > m)`, 
		MP_TAC(SPEC stmt holed_lem) THEN 
		IS_EXPR_TYPE_TAC THEN 
		EVAL_BETA_RED_TAC THEN 
		REWRITE_TAC[] THEN 
		CONSTRUCTION_TO_QUOTE_TAC THEN
		HOLE_ABSORB_TAC THEN
		LAW_OF_DISQUO_TAC THEN
		REWRITE_TAC[]);;





	
