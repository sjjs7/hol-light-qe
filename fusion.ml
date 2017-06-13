(* ========================================================================= *)
(* Complete HOL kernel of types, terms and theorems.                         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "lib.ml";;

module type Hol_kernel =
  sig
      type hol_type = private
        Tyvar of string
      | Tyapp of string *  hol_type list

      type term = private
        Var of string * hol_type
      | Const of string * hol_type
      | Comb of term * term
      | Abs of term * term
      | Quote of term * hol_type * (hol_type) list

      type thm

      val types: unit -> (string * int)list
      val get_type_arity : string -> int
      val new_type : (string * int) -> unit
      val mk_type: (string * hol_type list) -> hol_type
      val mk_vartype : string -> hol_type
      val dest_type : hol_type -> (string * hol_type list)
      val dest_vartype : hol_type -> string
      val is_type : hol_type -> bool
      val is_vartype : hol_type -> bool
      val tyvars : hol_type -> hol_type list
      val type_subst : (hol_type * hol_type)list -> hol_type -> hol_type
      val bool_ty : hol_type
      val aty : hol_type

      val constants : unit -> (string * hol_type) list
      val get_const_type : string -> hol_type
      val new_constant : string * hol_type -> unit
      val type_of : term -> hol_type
      val alphaorder : term -> term -> int
      val is_var : term -> bool
      val is_const : term -> bool
      val is_abs : term -> bool
      val is_comb : term -> bool
      val is_quote : term -> bool
      val mk_var : string * hol_type -> term
      val mk_const : string * (hol_type * hol_type) list -> term
      val mk_abs : term * term -> term
      val mk_comb : term * term -> term
      val mk_quote : term * (hol_type) list -> term
      val dest_var : term -> string * hol_type
      val dest_const : term -> string * hol_type
      val dest_comb : term -> term * term
      val dest_abs : term -> term * term
      val dest_quote: term -> term * (hol_type) list
      val frees : term -> term list
      val freesl : term list -> term list
      val freesin : term list -> term -> bool
      val vfree_in : term -> term -> bool
      val type_vars_in_term : term -> hol_type list
      val variant : term list -> term -> term
      val vsubst : (term * term) list -> term -> term
      val qsubst : (term * term) list -> term -> term
      val inst : (hol_type * hol_type) list -> term -> term
      val rand: term -> term
      val rator: term -> term
      val dest_eq: term -> term * term

      val dest_thm : thm -> term list * term
      val hyp : thm -> term list
      val concl : thm -> term
      val REFL : term -> thm
      val QUOTE : term -> thm
      val TERM_TO_CONSTRUCTION : term -> thm
      val QUOTE_CONV : term -> thm
      val TERM_TO_CONSTRUCTION_CONV : term -> thm
      val TRANS : thm -> thm -> thm
      val MK_COMB : thm * thm -> thm
      val ABS : term -> thm -> thm
      val BETA : term -> thm
      val ASSUME : term -> thm
      val EQ_MP : thm -> thm -> thm
      val DEDUCT_ANTISYM_RULE : thm -> thm -> thm
      val INST_TYPE : (hol_type * hol_type) list -> thm -> thm
      val INST : (term * term) list -> thm -> thm
      val axioms : unit -> thm list
      val new_axiom : term -> thm
      val definitions : unit -> thm list
      val new_basic_definition : term -> thm
      val new_basic_type_definition :
              string -> string * string -> thm -> thm * thm
      val hole_lookup : (hol_type * term) list ref
      val match_hole : hol_type -> (hol_type * term) list -> term
      val add_hole_def : hol_type -> term -> (hol_type * term) list -> unit
      val modify_hole_def : hol_type -> term -> (hol_type * term) list -> (hol_type * term) list -> unit
      val match_type : term -> (hol_type * term) list -> (hol_type list)
      val HOLE_CONV : term -> thm -> unit
      val getTyv : unit -> int
      val HOLE_THM_CONV : term -> thm -> thm
      val HOLE_THM_CONV_FIND : term -> thm -> thm
end;;

(* ------------------------------------------------------------------------- *)
(* This is the implementation of those primitives.                           *)
(* ------------------------------------------------------------------------- *)

module Hol : Hol_kernel = struct

  type hol_type = Tyvar of string
                | Tyapp of string *  hol_type list

  type term = Var of string * hol_type
            | Const of string * hol_type
            | Comb of term * term
            | Abs of term * term
            (*Current plan to mark holes is to replace them with "HOLE" constants whose type is a unique number type generated by HOL, 
            the list below can then map the constant back to the real term. Later, conversion functions and tactics will be added to interact with the elements in this list*)
            | Quote of term * hol_type * (hol_type) list

  type thm = Sequent of (term list * term)

(* ------------------------------------------------------------------------- *)
(* List of current type constants with their arities.                        *)
(*                                                                           *)
(* Initially we just have the boolean type and the function space            *)
(* constructor. Later on we add as primitive the type of individuals.        *)
(* All other new types result from definitional extension.                   *)
(* ------------------------------------------------------------------------- *)

  let the_type_constants = ref ["bool",0; "fun",2]

(* ------------------------------------------------------------------------- *)
(* Return all the defined types.                                             *)
(* ------------------------------------------------------------------------- *)

  let types() = !the_type_constants

(* ------------------------------------------------------------------------- *)
(* Lookup function for type constants. Returns arity if it succeeds.         *)
(* ------------------------------------------------------------------------- *)

  let get_type_arity s = assoc s (!the_type_constants)

(* ------------------------------------------------------------------------- *)
(* Declare a new type.                                                       *)
(* ------------------------------------------------------------------------- *)

  let new_type(name,arity) =
    if can get_type_arity name then
      failwith ("new_type: type "^name^" has already been declared")
    else the_type_constants := (name,arity)::(!the_type_constants)

(* ------------------------------------------------------------------------- *)
(* Basic type constructors.                                                  *)
(* ------------------------------------------------------------------------- *)

  let mk_type(tyop,args) =
    let arity = try get_type_arity tyop with Failure _ ->
      failwith ("mk_type: type "^tyop^" has not been defined") in
    if arity = length args then
      Tyapp(tyop,args)
    else failwith ("mk_type: wrong number of arguments to "^tyop)

  let mk_vartype v = Tyvar(v)

(* ------------------------------------------------------------------------- *)
(* Basic type destructors.                                                   *)
(* ------------------------------------------------------------------------- *)

  let dest_type =
    function
        (Tyapp (s,ty)) -> s,ty
      | (Tyvar _) -> failwith "dest_type: type variable not a constructor"

  let dest_vartype =
    function
        (Tyapp(_,_)) -> failwith "dest_vartype: type constructor not a variable"
      | (Tyvar s) -> s

(* ------------------------------------------------------------------------- *)
(* Basic type discriminators.                                                *)
(* ------------------------------------------------------------------------- *)

  let is_type = can dest_type

  let is_vartype = can dest_vartype

(* ------------------------------------------------------------------------- *)
(* Return the type variables in a type and in a list of types.               *)
(* ------------------------------------------------------------------------- *)

  let rec tyvars =
      function
          (Tyapp(_,args)) -> itlist (union o tyvars) args []
        | (Tyvar v as tv) -> [tv]

(* ------------------------------------------------------------------------- *)
(* Substitute types for type variables.                                      *)
(*                                                                           *)
(* NB: non-variables in subst list are just ignored (a check would be        *)
(* repeated many times), as are repetitions (first possibility is taken).    *)
(* ------------------------------------------------------------------------- *)

(*Todo: Remove the  prefix to restore normal operations*)

let rec type_subst i ty =
    match ty with
      Tyapp(tycon,args) ->
          let args' = qmap (type_subst i) args in
          if args' == args then ty else Tyapp(tycon,args')
      | _ -> rev_assocd ty i ty


  let bool_ty = Tyapp("bool",[])

  let aty = Tyvar "A"

(* ------------------------------------------------------------------------- *)
(* List of term constants and their types.                                   *)
(*                                                                           *)
(* We begin with just equality (over all types). Later, the Hilbert choice   *)
(* operator is added. All other new constants are defined.                   *)
(* ------------------------------------------------------------------------- *)

  let the_term_constants =
     ref ["=",Tyapp("fun",[aty;Tyapp("fun",[aty;bool_ty])]);"_Q_",Tyapp("fun",[aty;Tyapp("epsilon",[])]);"HOLE",Tyvar "match"]

  let hole_lookup = ref [];;

  let rec match_hole ty l = match l with
    | a :: rest -> if (fst a) = ty then (snd a) else match_hole ty rest
    | [] -> failwith "Undefined hole" 

  let rec add_hole_def ty tm l = match l with
    | a :: rest -> if ty <> (fst a) then add_hole_def ty tm rest else failwith "Cannot add two definitions for a single hole"
    | [] -> let () = hole_lookup := List.append !hole_lookup [(ty,tm)] in ();;

  let rec modify_hole_def ty tm l past = match l with
    | a :: rest -> if ty <> (fst a) then modify_hole_def ty tm rest (a :: past) else let () = hole_lookup := (List.append ((ty,tm) :: past) rest) in ()
    | [] -> failwith "Undefined hole";;

  (*Given a term, returns list of all types matching that term. *)

  let rec match_type trm l = match l with
    | a :: rest -> if (snd a) = trm then List.append (match_type trm rest) [(fst a)] else match_type trm rest
    | [] -> [];;

  (*Need to move the faculties for generating variable types from preterm to here for quote conversion to work*)
  let tyv_num = ref 0;;

  let getTyv unit = let () = tyv_num := (!tyv_num + 1) in !tyv_num;;

(* ------------------------------------------------------------------------- *)
(* Return all the defined constants with generic types.                      *)
(* ------------------------------------------------------------------------- *)

  let constants() = !the_term_constants

(* ------------------------------------------------------------------------- *)
(* Gets type of constant if it succeeds.                                     *)
(* ------------------------------------------------------------------------- *)

  let get_const_type s = assoc s (!the_term_constants)

(* ------------------------------------------------------------------------- *)
(* Declare a new constant.                                                   *)
(* ------------------------------------------------------------------------- *)

  let new_constant(name,ty) =
    if can get_const_type name then
      failwith ("new_constant: constant "^name^" has already been declared")
    else the_term_constants := (name,ty)::(!the_term_constants)

(* ------------------------------------------------------------------------- *)
(* Finds the type of a term (assumes it is well-typed).                      *)
(* ------------------------------------------------------------------------- *)

  let rec type_of tm =
    match tm with
      Var(_,ty) -> ty
    | Const("HOLE",ty) -> (match (match_hole ty !hole_lookup) with Quote(e,t,h) -> t | _ -> type_of (match_hole ty !hole_lookup))
    | Const(_,ty) -> ty
    | Comb(s,_) -> (match type_of s with Tyapp("fun",[dty;rty]) -> rty)
    | Abs(Var(_,ty),t) -> Tyapp("fun",[ty;type_of t])
    | Quote(e,_,_) -> Tyapp("epsilon",[])
    | _ -> failwith "TYPE_OF: Invalid term. You should not see this error under normal use, if you do, the parser has allowed an ill formed term to be created."

(* ------------------------------------------------------------------------- *)
(* Primitive discriminators.                                                 *)
(* ------------------------------------------------------------------------- *)

  let is_var = function (Var(_,_)) -> true | _ -> false

  let is_const = function (Const(_,_)) -> true | _ -> false

  let is_abs = function (Abs(_,_)) -> true | _ -> false

  let is_comb = function (Comb(_,_)) -> true | _ -> false

  let is_quote = function (Quote(_,_,_)) -> true | _ -> false

(* ------------------------------------------------------------------------- *)
(* Primitive constructors.                                                   *)
(* ------------------------------------------------------------------------- *)

  let mk_var(v,ty) = Var(v,ty)

  let mk_const(name,theta) =
    let uty = try get_const_type name with Failure _ ->
      failwith "mk_const: not a constant name" in
    Const(name,type_subst theta uty)

  let mk_abs(bvar,bod) =
    match bvar with
      Var(_,_) -> Abs(bvar,bod)
    | _ -> failwith "mk_abs: not a variable"


  let mk_comb(f,a) =
    match type_of f with
      Tyapp("fun",[ty;_]) when Pervasives.compare ty (type_of a) = 0
        -> Comb(f,a)
    | _ -> failwith "mk_comb: types do not agree"

  let mk_quote t,h = Quote(t,type_of t,h)

(* ------------------------------------------------------------------------- *)
(* Primitive destructors.                                                    *)
(* ------------------------------------------------------------------------- *)

  let dest_var =
    function (Var(s,ty)) -> s,ty | _ -> failwith "dest_var: not a variable"

  let dest_const =
    function (Const(s,ty)) -> s,ty | _ -> failwith "dest_const: not a constant"

  let dest_comb =
    function (Comb(f,x)) -> f,x | _ -> failwith "dest_comb: not a combination"

  let dest_abs =
    function (Abs(v,b)) -> v,b | _ -> failwith "dest_abs: not an abstraction"

  let dest_quote =
    function (Quote(e,ty,sl)) when type_of e = ty -> e,sl | _ -> failwith "dest_quote: not a quotation or type mismatch"

(* ------------------------------------------------------------------------- *)
(* Finds the variables free in a term (list of terms).                       *)
(* ------------------------------------------------------------------------- *)

  let rec frees tm =
    match tm with
      Var(_,_) -> [tm]
    | Const(_,_) -> []
    | Abs(bv,bod) -> subtract (frees bod) [bv]
    | Comb(s,t) -> union (frees s) (frees t)
    | Quote(_,_,_) -> []

  let freesl tml = itlist (union o frees) tml []

(* ------------------------------------------------------------------------- *)
(* Whether all free variables in a term appear in a list.                    *)
(* ------------------------------------------------------------------------- *)

  let rec freesin acc tm =
    match tm with
      Var(_,_) -> mem tm acc
    | Const(_,_) -> true
    | Abs(bv,bod) -> freesin (bv::acc) bod
    | Comb(s,t) -> freesin acc s && freesin acc t
    | Quote(_,_,_) -> true (*Quotes have no free variables, [] is a subset of every list, therefore this should be true*)

(* ------------------------------------------------------------------------- *)
(* Whether a variable (or constant in fact) is free in a term.               *)
(* ------------------------------------------------------------------------- *)

  let rec vfree_in v tm =
    match tm with
      Abs(bv,bod) -> v <> bv && vfree_in v bod
    | Comb(s,t) -> vfree_in v s || vfree_in v t
    | Quote(_,_,_) -> false
    | _ -> Pervasives.compare tm v = 0

(* ------------------------------------------------------------------------- *)
(* Finds the type variables (free) in a term.                                *)
(* ------------------------------------------------------------------------- *)

  let rec type_vars_in_term tm =
    match tm with
      Var(_,ty)        -> tyvars ty
    | Const(_,ty)      -> tyvars ty
    | Comb(s,t)        -> union (type_vars_in_term s) (type_vars_in_term t)
    | Abs(Var(_,ty),t) -> union (tyvars ty) (type_vars_in_term t)
    | Quote(_,_,_)         -> tyvars (Tyapp ("epsilon",[]))
    | _                -> failwith "TYPE_VARS_IN_TERM: Invalid type."

(* ------------------------------------------------------------------------- *)
(* For name-carrying syntax, we need this early.                             *)
(* ------------------------------------------------------------------------- *)

  let rec variant avoid v =
    if not(exists (vfree_in v) avoid) then v else
    match v with
      Var(s,ty) -> variant avoid (Var(s^"'",ty))
    | _ -> failwith "variant: not a variable"

(* ------------------------------------------------------------------------- *)
(* Substitution primitive (substitution for variables only!)                 *)
(* ------------------------------------------------------------------------- *)
  
      (*Function to handle substitutions in holes in quotations*)
  let rec qsubst ilist tm =

    let rec vsubst ilist tm =
      match tm with
      | Var(_,_) -> rev_assocd tm ilist tm
      | Const(_,_) -> tm
      | Quote(_,_,_) -> tm
      | Comb(Const("_Q_",Tyapp ("fun",[_;Tyapp ("epsilon",[])])),_) -> tm
      | Comb(s,t) -> let s' = vsubst ilist s and t' = vsubst ilist t in
                     if s' == s && t' == t then tm else Comb(s',t')
      | Abs(v,s) -> let ilist' = filter (fun (t,x) -> x <> v) ilist in
                    if ilist' = [] then tm else
                    let s' = vsubst ilist' s in
                    if s' == s then tm else
                    if exists (fun (t,x) -> vfree_in v t && vfree_in x s) ilist'
                    then let v' = variant [s'] v in
                         Abs(v',vsubst ((v',v)::ilist') s)
                    else Abs(v,s') in
    match tm with
    | Quote(e,ty,h) -> Quote(qsubst ilist e,ty,h)
    | Comb(s,t) -> let s' = qsubst ilist s and t' = qsubst ilist t in
                     if s' == s && t' == t then tm else Comb(s',t')
    | Const("HOLE",ty) -> let h' = vsubst ilist (match_hole ty !hole_lookup) in
                          let nt = mk_vartype ("?" ^ string_of_int (getTyv ())) in
                          let () = add_hole_def nt h' !hole_lookup in
                          Const("HOLE",nt)
    | _ -> tm 

  let vsubst =

    let rec vsubst ilist tm =
      match tm with
      | Var(_,_) -> rev_assocd tm ilist tm
      | Const(_,_) -> tm
      | Quote(e,ty,h) -> Quote(qsubst ilist e,ty,h)
      | Comb(Const("_Q_",Tyapp ("fun",[_;Tyapp ("epsilon",[])])),_) -> tm
      | Comb(s,t) -> let s' = vsubst ilist s and t' = vsubst ilist t in
                     if s' == s && t' == t then tm else Comb(s',t')
      | Abs(v,s) -> let ilist' = filter (fun (t,x) -> x <> v) ilist in
                    if ilist' = [] then tm else
                    let s' = vsubst ilist' s in
                    if s' == s then tm else
                    if exists (fun (t,x) -> vfree_in v t && vfree_in x s) ilist'
                    then let v' = variant [s'] v in
                         Abs(v',vsubst ((v',v)::ilist') s)
                    else Abs(v,s') in
    fun theta ->
      if theta = [] then (fun tm -> tm) else
      if forall (function (t,Var(_,y)) -> Pervasives.compare (type_of t) y = 0
                        | _ -> false) theta
      then vsubst theta else failwith "vsubst: Bad substitution list"

(* ------------------------------------------------------------------------- *)
(* Type instantiation primitive.                                             *)
(* ------------------------------------------------------------------------- *)

  exception Clash of term

  let inst =
    let rec inst env tyin tm =
      match tm with
        Var(n,ty)   -> let ty' = type_subst tyin ty in
                       let tm' = if ty' == ty then tm else Var(n,ty') in
                       if Pervasives.compare (rev_assocd tm' env tm) tm = 0
                       then tm'
                       else raise (Clash tm')
      | Const(c,ty) -> let ty' = type_subst tyin ty in
                       if ty' == ty then tm else Const(c,ty')
      | Quote(_,_,_)    -> tm
      | Comb(Const("_Q_",Tyapp ("fun",[_;Tyapp ("epsilon",[])])),_) -> tm
      | Comb(f,x)   -> let f' = inst env tyin f and x' = inst env tyin x in
                       if f' == f && x' == x then tm else Comb(f',x')
      | Abs(y,t)    -> let y' = inst [] tyin y in
                       let env' = (y,y')::env in
                       try let t' = inst env' tyin t in
                           if y' == y && t' == t then tm else Abs(y',t')
                       with (Clash(w') as ex) ->
                       if w' <> y' then raise ex else
                       let ifrees = map (inst [] tyin) (frees t) in
                       let y'' = variant ifrees y' in
                       let z = Var(fst(dest_var y''),snd(dest_var y)) in
                       inst env tyin (Abs(z,vsubst[z,y] t)) in
    fun tyin -> if tyin = [] then fun tm -> tm else inst [] tyin

(* ------------------------------------------------------------------------- *)
(* A few bits of general derived syntax.                                     *)
(* ------------------------------------------------------------------------- *)

  let rator tm =
    match tm with
      Comb(l,r) -> l
    | _ -> failwith "rator: Not a combination"

  let rand tm =
    match tm with
      Comb(l,r) -> r
    | _ -> failwith "rand: Not a combination"

(* ------------------------------------------------------------------------- *)
(* Syntax operations for equations.                                          *)
(* ------------------------------------------------------------------------- *)

  let safe_mk_eq l r =
    let ty = type_of l in
    Comb(Comb(Const("=",Tyapp("fun",[ty;Tyapp("fun",[ty;bool_ty])])),l),r)

  let dest_eq tm =
    match tm with
      Comb(Comb(Const("=",_),l),r) -> l,r
    | _ -> failwith "dest_eq"

(* ------------------------------------------------------------------------- *)
(* Useful to have term union modulo alpha-conversion for assumption lists.   *)
(* ------------------------------------------------------------------------- *)

  (*Attempts to look up the thm's hole resolutions, *)
  let rec checkHole tm1 tm2 =
  let ty1 = snd (dest_const (tm1)) in
  let ty2 = snd (dest_const (tm2)) in
  let res1 = match_hole ty1 !hole_lookup in
  let res2 = match_hole ty2 !hole_lookup in
  Pervasives.compare res1 res2;;


  let rec ordav env x1 x2 =
    match env with
      [] -> Pervasives.compare x1 x2
    | (t1,t2)::oenv -> if Pervasives.compare x1 t1 = 0
                       then if Pervasives.compare x2 t2 = 0
                            then 0 else -1
                       else if Pervasives.compare x2 t2 = 0 then 1
                       else ordav oenv x1 x2

  let rec orda env tm1 tm2 =
    if tm1 == tm2 && forall (fun (x,y) -> x = y) env then 0 else
    match (tm1,tm2) with
      Var(x1,ty1),Var(x2,ty2) -> ordav env tm1 tm2
    | Const(x1,ty1),Const(x2,ty2) -> if x1 = "HOLE" && x2 = "HOLE" then checkHole tm1 tm2 else Pervasives.compare tm1 tm2
    | Comb(s1,t1),Comb(s2,t2) ->
          let c = orda env s1 s2 in if c <> 0 then c else orda env t1 t2
    | Abs(Var(_,ty1) as x1,t1),Abs(Var(_,ty2) as x2,t2) ->
          let c = Pervasives.compare ty1 ty2 in
          if c <> 0 then c else orda ((x1,x2)::env) t1 t2
    | Quote(e1,_,_),Quote(e2,_,_) -> orda env e1 e2
    | Const(_,_),_ -> -1
    | _,Const(_,_) -> 1
    | Var(_,_),_ -> -1
    | _,Var(_,_) -> 1
    | Comb(_,_),_ -> -1
    | _,Comb(_,_) -> 1
    | Quote(_,_,_),_ -> 1
    | _,Quote(_,_,_) -> -1  

  let alphaorder = orda []

  let rec term_union l1 l2 =
    match (l1,l2) with
      ([],l2) -> l2
    | (l1,[]) -> l1
    | (h1::t1,h2::t2) -> let c = alphaorder h1 h2 in
                         if c = 0 then h1::(term_union t1 t2)
                         else if c < 0 then h1::(term_union t1 l2)
                         else h2::(term_union l1 t2)

  let rec term_remove t l =
    match l with
      s::ss -> let c = alphaorder t s in
               if c > 0 then
                 let ss' = term_remove t ss in
                 if ss' == ss then l else s::ss'
               else if c = 0 then ss else l
    | [] -> l

  let rec term_image f l =
    match l with
      h::t -> let h' = f h and t' = term_image f t in
              if h' == h && t' == t then l else term_union [h'] t'
    | [] -> l

(* ------------------------------------------------------------------------- *)
(* Basic theorem destructors.                                                *)
(* ------------------------------------------------------------------------- *)

  let dest_thm (Sequent(asl,c)) = (asl,c)

  let hyp (Sequent(asl,c)) = asl

  let concl (Sequent(asl,c)) = c

(* ------------------------------------------------------------------------- *)
(* Basic equality properties; TRANS is derivable but included for efficiency *)
(* ------------------------------------------------------------------------- *)

  let REFL tm =
    Sequent([],safe_mk_eq tm tm)

  let TRANS (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    match (c1,c2) with
      Comb((Comb(Const("=",_),_) as eql),m1),Comb(Comb(Const("=",_),m2),r)
        when alphaorder m1 m2 = 0 -> Sequent(term_union asl1 asl2,Comb(eql,r))
    | _ -> failwith "TRANS"

(* ------------------------------------------------------------------------- *)
(* Congruence properties of equality.                                        *)
(* ------------------------------------------------------------------------- *)

  let MK_COMB(Sequent(asl1,c1),Sequent(asl2,c2)) =
     match (c1,c2) with
       Comb(Comb(Const("=",_),l1),r1),Comb(Comb(Const("=",_),l2),r2) ->
        (match type_of r1 with
           Tyapp("fun",[ty;_]) when Pervasives.compare ty (type_of r2) = 0
             -> Sequent(term_union asl1 asl2,
                        safe_mk_eq (Comb(l1,l2)) (Comb(r1,r2)))
         | _ -> failwith "MK_COMB: types do not agree")
     | _ -> failwith "MK_COMB: not both equations"

  let ABS v (Sequent(asl,c)) =
    match (v,c) with
      Var(_,_),Comb(Comb(Const("=",_),l),r) when not(exists (vfree_in v) asl)
         -> Sequent(asl,safe_mk_eq (Abs(v,l)) (Abs(v,r)))
    | _ -> failwith "ABS";;

(* ------------------------------------------------------------------------- *)
(* Trivial case of lambda calculus beta-conversion.                          *)
(* ------------------------------------------------------------------------- *)

  let BETA tm =
    match tm with
      Comb(Abs(v,bod),arg) when Pervasives.compare arg v = 0
        -> Sequent([],safe_mk_eq tm bod)
    | _ -> failwith "BETA: not a trivial beta-redex"

(* ------------------------------------------------------------------------- *)
(* Rules connected with deduction.                                           *)
(* ------------------------------------------------------------------------- *)

  let ASSUME tm =
    if Pervasives.compare (type_of tm) bool_ty = 0 then Sequent([tm],tm)
    else failwith "ASSUME: not a proposition"

  let EQ_MP (Sequent(asl1,eq)) (Sequent(asl2,c)) =
    match eq with
      Comb(Comb(Const("=",_),l),r) when alphaorder l c = 0
        -> Sequent(term_union asl1 asl2,r)
    | _ -> failwith "EQ_MP"

  let DEDUCT_ANTISYM_RULE (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    let asl1' = term_remove c2 asl1 and asl2' = term_remove c1 asl2 in
    Sequent(term_union asl1' asl2',safe_mk_eq c1 c2)

(* ------------------------------------------------------------------------- *)
(* Type and term instantiation.                                              *)
(* ------------------------------------------------------------------------- *)

  let INST_TYPE theta (Sequent(asl,c)) =
    let inst_fn = inst theta in
    Sequent(term_image inst_fn asl,inst_fn c)

  let INST theta (Sequent(asl,c)) =
    let inst_fun = vsubst theta in
    Sequent(term_image inst_fun asl,inst_fun c)

(* ------------------------------------------------------------------------- *)
(* Quotation handling.                                                       *)
(* ------------------------------------------------------------------------- *)

(*First a bunch of definitions normally defined later during HOL's startup process must be defined*)
(*The purpose of all these is to implement an early version of mk_string so that epsilon's type types may be constructed*)
  let makeConstructedType name list = (Tyapp (name,list));;
  let makeBasicType name = makeConstructedType name [];;
  let makeFalse = Const("F",(makeBasicType "bool"));;
  let makeTrue = Const("T",(makeBasicType "bool"));;
  (*This makes a function called ASCII of type bool->bool->bool->bool->bool->bool->bool->bool->char*)
  let makeAscii = Const("ASCII",(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [
(makeBasicType "bool");(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [
(makeBasicType "bool");(makeBasicType "char")])])])])
])])])]));;
  (*This makes a function called CONS of type char -> (list)char -> list(char)*)
  let makeCONS = Const("CONS",makeConstructedType "fun" [makeBasicType "char"; makeConstructedType "fun" [makeConstructedType "list" [makeBasicType "char"];makeConstructedType "list" [makeBasicType "char"]]]);;
  
  let numToBool = function
    | 1 -> makeTrue
    | 0 -> makeFalse
    | _ -> failwith "Cannot convert this number to a boolean value"

(*Converts a char value to a combination of T's and F's representing the binary form of it's ASCII value (HOL stores it this way)*)

  let rec charToHOL c depth = if depth < 8 then Comb((charToHOL (c / 2) (depth + 1)),(numToBool (c mod 2)))
  else Comb(makeAscii,(numToBool (c mod 2)));;

(*Takes an exploded string and turns it into a HOL string*)
  let rec tmp_mk_string = function
    | [] -> Const("NIL",makeConstructedType "list" [makeBasicType "char"])
    | a :: rest -> Comb(Comb(makeCONS,(charToHOL (Char.code (a.[0])) 1)),(tmp_mk_string rest));;


  (*Need a temporary implementation of mk_string and related functions*)

  (*Helper functions to make vital functions more readable*)
  let makeHolFunction a b = Tyapp("fun",[a;b]);;
  let makeHolType a b = Tyapp(a,b)
  let makeGenericComb constName ty firstArg secondArg = Comb(Comb(Const(constName,ty),firstArg),secondArg);;
  let makeQuoVarComb a b = makeGenericComb "QuoVar" (makeHolFunction (makeHolType "list" [makeHolType "char" []]) (makeHolFunction (makeHolType "type" []) (makeHolType "epsilon" [])) ) (tmp_mk_string (explode a)) b;;
  let makeQuoConstComb a b = makeGenericComb "QuoConst" (makeHolFunction (makeHolType "list" [makeHolType "char" []]) (makeHolFunction (makeHolType "type" []) (makeHolType "epsilon" [])) ) (tmp_mk_string (explode a)) b;;
  let makeAppComb a b = makeGenericComb "App" (makeHolFunction (makeHolType "epsilon" []) (makeHolFunction (makeHolType "epsilon" []) (makeHolType "epsilon" []))) a b;;
  let makeAbsComb a b = makeGenericComb "Abs" (makeHolFunction (makeHolType "epsilon" []) (makeHolFunction (makeHolType "epsilon" []) (makeHolType "epsilon" []))) a b;;
  let makeTyVarComb a = Comb(Const("TyVar",makeConstructedType "fun" [makeConstructedType "list" [makeBasicType "char"];makeBasicType "type"]),(tmp_mk_string (explode a)));;
  let makeTyBaseComb a  = Comb(Const("TyBase",makeConstructedType "fun" [makeConstructedType "list" [makeBasicType "char"];makeBasicType "type"]),(tmp_mk_string (explode a)));;
  let makeTyMonoConsComb a b = makeGenericComb "TyMonoCons" (makeHolFunction (makeHolType "list" [makeHolType "char" []]) (makeHolFunction (makeHolType "type" []) (makeHolType "type" []))) (tmp_mk_string (explode a)) b;;
  let makeTyBiConsComb a b c= Comb((makeGenericComb "TyBiCons" (makeHolFunction (makeHolType "list" [makeHolType "char" []]) (makeHolFunction (makeHolType "type" []) (makeHolFunction (makeHolType "type" []) (makeHolType "type" [])))) (tmp_mk_string (explode a)) b),c);;
  let makeFunComb a b = makeTyBiConsComb "fun" a b;;
  let makeQuoComb a = Comb(Const("Quo",(makeHolFunction (makeHolType "epsilon" []) (makeHolType "epsilon" []))),a);;

  let rec matchType ty = 
      if (is_vartype ty) then makeTyVarComb (dest_vartype ty) else
        let a,b = (dest_type ty) in
        match length b with
          | 0 -> makeTyBaseComb a
          | 1 -> makeTyMonoConsComb a (matchType (hd b))
          | 2 -> makeTyBiConsComb a (matchType (hd b)) (matchType (hd (tl b)))
          | _ -> failwith "This is not a valid type";;


  (*Currently in development - will always return False for now for testing purposes*)
  let rec termToConstruction = function
      |  Const(cName,cType) -> makeQuoConstComb cName (matchType cType)
      |  Var(vName,vType) -> makeQuoVarComb vName (matchType vType)
      |  Comb(exp1, exp2) -> makeAppComb (termToConstruction exp1) (termToConstruction exp2)
      |  Abs(exp1, exp2) -> makeAbsComb (termToConstruction exp1) (termToConstruction exp2)
      |  Quote(e,t,[]) when type_of e = t -> makeQuoComb (termToConstruction e)
      |  Quote _ -> failwith "Quotation must have all holes filled in before it can be used" (*Todo: Implement some way to allow quotes in quotes to have holes*)
      |  _ -> failwith "Malformed term cannot be made into a construction"

  let TERM_TO_CONSTRUCTION tm = match tm with
      |  Quote(exp,t,h) when type_of exp = t -> Sequent([],safe_mk_eq tm (termToConstruction exp))
      |  Quote(_,_,_) -> failwith "TERM_TO_CONSTRUCTION: BAD QUOTE"
      | _ -> failwith "TERM_TO_CONSTRUCTION"
  
  (*Returns a theorem asserting that the quotation of a term is equivelant to wrapping Quote around it*)
  (*i.e. _Q_ P <=> (Q(P)Q)*)   
  let QUOTE tm = match tm with
      |  Comb(Const("_Q_",Tyapp("fun",[_;(Tyapp ("epsilon",[]))])),qtm) -> Sequent([],safe_mk_eq tm (Quote (qtm,type_of qtm,[])))
      |  _ -> failwith "QUOTE"

  (*These conversion functions can be used on their own but mainly will be used to construct tactics. They will search through a term for the first applicable instance and return the result of applying
  the relevant function to it*)

  let rec QUOTE_CONV tm = match tm with
    | Const(a,b) -> failwith "QUOTE_CONV"
    | Comb(Const("_Q_",Tyapp("fun",[_;(Tyapp ("epsilon",[]))])),_) -> QUOTE tm
    | Comb(a,b) -> try QUOTE_CONV a with Failure _ -> try QUOTE_CONV b with Failure _ -> failwith "QUOTE_CONV"
    | _ -> failwith "QUOTE_CONV"

  let rec TERM_TO_CONSTRUCTION_CONV tm = match tm with
    | Const(a,b) -> failwith "TERM_TO_CONSTRUCTION_CONV"
    | Quote(_,_,_) -> TERM_TO_CONSTRUCTION tm
    | Comb(a,b) -> try TERM_TO_CONSTRUCTION_CONV a with Failure _ -> try TERM_TO_CONSTRUCTION_CONV b with Failure _ -> failwith "TERM_TO_CONSTRUCTION_CONV"
    | _ -> failwith "TERM_TO_CONSTRUCTION_CONV"

(*For performing operations on holes inside quotations - this method does not give a theorem but instead directly modifies the quotation, it is meant for quick testing and will be removed from
  the public interface (i.e. inaccessible to functions outside the kernel) when proper theorem/tactic functions have been introduced*)
  let HOLE_CONV quote tm =
    let rec replace_thm old rep l = match l with
      | a :: rest -> modify_hole_def a rep !hole_lookup []
      | [] -> failwith "HOLE_CONV" 
    in
    let locals = snd (dest_quote quote) in
    let matches = List.filter (fun a -> mem a locals) (match_type (fst (dest_eq (concl tm))) !hole_lookup) in
    replace_thm (fst (dest_eq (concl tm))) (snd (dest_eq (concl tm))) matches

  let rec twoListsToPairs l1 l2 = 
    let () = assert (List.length l1 = List.length l2) in
      match l1 with 
        | a :: rest -> (List.hd l1, List.hd l2) :: (twoListsToPairs (List.tl l1) (List.tl l2))
        | [] -> [];; 

  let rec lookupReplacementType t1 l = match l with
    | a :: rest -> if (fst a) = t1 then snd a else lookupReplacementType t1 rest
    | [] -> failwith "Could not find match for type";;

  let rec mkUpdatedQuote expr updates = match expr with
    | Quote (a,ty,h) -> Quote (a,ty,h)
    | Var (a,ty) -> Var (a,ty)
    | Comb(l,r) -> Comb(mkUpdatedQuote l updates, mkUpdatedQuote r updates)
    | Abs(l,r) -> Abs(mkUpdatedQuote l updates, mkUpdatedQuote r updates)   
    | Const(a,ty) -> Const(a, (lookupReplacementType ty updates));;

  (*For making a theorem out of hole conversion - CURRENTLY BUGGY, NEEDS FIXING*)
  let HOLE_THM_CONV quote (tm:thm) = 
    if type_of (rand (rator (concl tm))) = mk_type("epsilon",[]) && type_of (rand (concl tm)) = mk_type("epsilon",[]) then
    (*Need to take apart the given quote*)
    let e,tys = dest_quote quote in
    (*Assign new types to the new HOLE constants*)
    let newL = List.map (fun a -> 
     let newvar = mk_vartype ("?" ^ (string_of_int (getTyv ()))) in
     let () = add_hole_def newvar (match_hole a !hole_lookup) !hole_lookup in
     newvar
     ) tys in
    let consMapping = twoListsToPairs tys newL in
    (*Create new quotation*)
    let newquo = mk_quote(mkUpdatedQuote e consMapping,newL) in
    (*Overwrite the cloned type variables with the applied theorem*)
    let () = HOLE_CONV newquo tm in 
    (*Generate and return theorem*)
    Sequent([],safe_mk_eq quote newquo)
  else failwith "HOLE_THM_CONV: THEOREM MUST EQUATE TWO EPSILON TERMS"
     
  (*In development, not yet working*)  
  let rec HOLE_THM_CONV_FIND trm (tm:thm) = if type_of (rand (rator (concl tm))) = mk_type("epsilon",[]) && type_of (rand (concl tm)) = mk_type("epsilon",[]) then
    (match trm with
    | Quote(e,t,h) -> HOLE_THM_CONV trm tm
    | Comb(l,r) -> try (HOLE_THM_CONV_FIND l tm) with Failure _ -> HOLE_THM_CONV_FIND r tm
    | _ -> failwith "HOLE_THM_CONV_FIND")
  else failwith "HOLE_THM_CONV_FIND: THEOREM MUST EQUATE TWO EPSILON TERMS"
     



(* ------------------------------------------------------------------------- *)
(* Handling of axioms.                                                       *)
(* ------------------------------------------------------------------------- *)

  let the_axioms = ref ([]:thm list)

  let axioms() = !the_axioms

  let new_axiom tm =
    if Pervasives.compare (type_of tm) bool_ty = 0 then
      let th = Sequent([],tm) in
       (the_axioms := th::(!the_axioms); th)
    else failwith "new_axiom: Not a proposition"

(* ------------------------------------------------------------------------- *)
(* Handling of (term) definitions.                                           *)
(* ------------------------------------------------------------------------- *)

  let the_definitions = ref ([]:thm list)

  let definitions() = !the_definitions

  let new_basic_definition tm =
    match tm with
      Comb(Comb(Const("=",_),Var(cname,ty)),r) ->
        if not(freesin [] r) then failwith "new_definition: term not closed"
        else if not (subset (type_vars_in_term r) (tyvars ty))
        then failwith "new_definition: Type variables not reflected in constant"
        else let c = new_constant(cname,ty); Const(cname,ty) in
             let dth = Sequent([],safe_mk_eq c r) in
             the_definitions := dth::(!the_definitions); dth
    | _ -> failwith "new_basic_definition"

(* ------------------------------------------------------------------------- *)
(* Handling of type definitions.                                             *)
(*                                                                           *)
(* This function now involves no logical constants beyond equality.          *)
(*                                                                           *)
(*             |- P t                                                        *)
(*    ---------------------------                                            *)
(*        |- abs(rep a) = a                                                  *)
(*     |- P r = (rep(abs r) = r)                                             *)
(*                                                                           *)
(* Where "abs" and "rep" are new constants with the nominated names.         *)
(* ------------------------------------------------------------------------- *)

  let new_basic_type_definition tyname (absname,repname) (Sequent(asl,c)) =
    if exists (can get_const_type) [absname; repname] then
      failwith "new_basic_type_definition: Constant(s) already in use" else
    if not (asl = []) then
      failwith "new_basic_type_definition: Assumptions in theorem" else
    let P,x = try dest_comb c
              with Failure _ ->
                failwith "new_basic_type_definition: Not a combination" in
    if not(freesin [] P) then
      failwith "new_basic_type_definition: Predicate is not closed" else
    let tyvars = sort (<=) (type_vars_in_term P) in
    let _ = try new_type(tyname,length tyvars)
            with Failure _ ->
                failwith "new_basic_type_definition: Type already defined" in
    let aty = Tyapp(tyname,tyvars)
    and rty = type_of x in
    let absty = Tyapp("fun",[rty;aty]) and repty = Tyapp("fun",[aty;rty]) in
    let abs = (new_constant(absname,absty); Const(absname,absty))
    and rep = (new_constant(repname,repty); Const(repname,repty)) in
    let a = Var("a",aty) and r = Var("r",rty) in
    Sequent([],safe_mk_eq (Comb(abs,mk_comb(rep,a))) a),
    Sequent([],safe_mk_eq (Comb(P,r))
                          (safe_mk_eq (mk_comb(rep,mk_comb(abs,r))) r))

end;;

include Hol;;

(* ------------------------------------------------------------------------- *)
(* Stuff that didn't seem worth putting in.                                  *)
(* ------------------------------------------------------------------------- *)

let mk_fun_ty ty1 ty2 = mk_type("fun",[ty1; ty2]);;
let bty = mk_vartype "B";;

let is_eq tm =
  match tm with
    Comb(Comb(Const("=",_),_),_) -> true
  | _ -> false;;

let mk_eq =
  let eq = mk_const("=",[]) in
  fun (l,r) ->
    try let ty = type_of l in
        let eq_tm = inst [ty,aty] eq in
        mk_comb(mk_comb(eq_tm,l),r)
    with Failure _ -> failwith "mk_eq";;

(* ------------------------------------------------------------------------- *)
(* Tests for alpha-convertibility (equality ignoring names in abstractions). *)
(* ------------------------------------------------------------------------- *)

let aconv s t = alphaorder s t = 0;;

(* ------------------------------------------------------------------------- *)
(* Comparison function on theorems. Currently the same as equality, but      *)
(* it's useful to separate because in the proof-recording version it isn't.  *)
(* ------------------------------------------------------------------------- *)

let equals_thm th th' = dest_thm th = dest_thm th';;
