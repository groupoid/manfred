(* Manfred Broy "Informatik" BNF + Pi/Sigma extension *)

open Printf

type term =
  | Var of string
  | Universe of int
  | Pi of string * term * term
  | Lam of string * term * term
  | App of term * term
  | Sigma of string * term * term
  | Pair of term * term
  | Fst of term
  | Snd of term

let rec string_of_term = function
  | Var x -> x
  | Universe u -> "U" ^ string_of_int u
  | Pi (x, a, b) -> "Π(" ^ x ^ ":" ^ string_of_term a ^ ")." ^ string_of_term b
  | Lam (x, a, t) -> "λ(" ^ x ^ ":" ^ string_of_term a ^ ")." ^ string_of_term t
  | App (t1, t2) -> "(" ^ string_of_term t1 ^ " " ^ string_of_term t2 ^ ")"
  | Sigma (x, a, b) -> "Σ(" ^ x ^ ":" ^ string_of_term a ^ ")." ^ string_of_term b
  | Pair (t1, t2) -> "(" ^ string_of_term t1 ^ ", " ^ string_of_term t2 ^ ")"
  | Fst t -> "fst " ^ string_of_term t
  | Snd t -> "snd " ^ string_of_term t

type context = (string * term) list

let universe = function Universe i -> i | _ -> failwith "Expected universe"

let rec subst x s = function
  | Var y -> if x = y then s else Var y
  | Pi (y, a, b) when x <> y -> Pi (y, subst x s a, subst x s b)
  | Sigma (y, a, b) when x <> y -> Sigma (y, subst x s a, subst x s b)
  | Lam (y, a, b) when x <> y -> Lam (y, subst x s a, subst x s b)
  | App (f, a) -> App (subst x s f, subst x s a)
  | Pair (t1, t2) -> Pair (subst x s t1, subst x s t2)
  | Fst t -> Fst (subst x s t)
  | Snd t -> Snd (subst x s t)
  | t -> t

let rec lookup x = function
  | [] -> failwith ("Unbound: " ^ x)
  | (y, typ) :: rest -> if x = y then typ else lookup x rest

let rec equal ctx t1 t2 = match t1, t2 with
  | Var x, Var y -> x = y
  | Universe i, Universe j -> i <= j
  | Pi (x, a, b), Pi (y, a', b') | Sigma (x, a, b), Sigma (y, a', b') ->
      equal ctx a a' && equal ((x, a) :: ctx) b (subst y (Var x) b')
  | Lam (x, _, b), t | t, Lam (x, _, b) -> equal ctx b (App (t, Var x))
  | Lam (x, a, b), Lam (y, a', b') -> equal ctx a a' && equal ((x,a)::ctx) b (subst y (Var x) b')
  | Pair (a1, b1), Pair (a2, b2) -> equal ctx a1 a2 && equal ctx b1 b2
  | Fst t1, Fst t2 | Snd t1, Snd t2 -> equal ctx t1 t2
  | App (f, a), App (f', a') -> equal ctx f f' && equal ctx a a'
  | _ -> false

and reduce ctx t = match t with
  | App (Lam (x, _, b), a) -> subst x a b
  | Fst (Pair (a, _)) -> a
  | Snd (Pair (_, b)) -> b
  | App (f, a) -> App (reduce ctx f, reduce ctx a)
  | Fst t -> Fst (reduce ctx t)
  | Snd t -> Snd (reduce ctx t)
  | Pair (t1, t2) -> Pair (reduce ctx t1, reduce ctx t2)
  | _ -> t

and normalize ctx t =
  let t' = reduce ctx t in
  if equal ctx t t' then t else normalize ctx t'

and infer ctx t =
  let res = match t with
    | Var x -> lookup x ctx
    | Universe i -> Universe (i + 1)
    | Pi (x, a, b) | Sigma (x, a, b) ->
        Universe (max (universe (infer ctx a)) (universe (infer ((x,a)::ctx) b)))
    | Lam (x, a, b) ->
        let _ = infer ctx a in Pi (x, a, infer ((x,a)::ctx) b)
    | App (f, a) -> (match infer ctx f with
        | Pi (x, _, b) -> subst x a b
        | _ -> failwith "Requires Π type")
    | Pair (t1, t2) ->
        let a = infer ctx t1 in Sigma ("_", a, infer ctx t2)
    | Fst t -> (match infer ctx t with Sigma (_, a, _) -> a | _ -> failwith "Fst requires Σ")
    | Snd t -> (match infer ctx t with Sigma (x, _, b) -> subst x (Fst t) b | _ -> failwith "Snd requires Σ")
  in normalize ctx res

(* ====================== BROY BNF → CORE ====================== *)
type broy_exp =
  | BId of string
  | BFunApp of string * broy_exp list
  | BIf of broy_exp * broy_exp * (broy_exp * broy_exp) list * broy_exp
  | BUnary of string * broy_exp
  | BBinary of broy_exp * string * broy_exp
  | BSection of broy_inner
  | BParens of broy_exp

and broy_inner =
  | BTypeExp of string * broy_exp
  | BElement of string * string * broy_exp
  | BFunDefs of (string * broy_exp) list * broy_exp
  | BIfInner of broy_exp * broy_exp * (broy_exp * broy_exp) list * broy_exp

let rec broy_to_core (e : broy_exp) : term = match e with
  | BId x -> Var x
  | BFunApp (f, args) ->
      List.fold_left (fun acc arg -> App (acc, broy_to_core arg)) (Var f) args
  | BIf (c, t, elifs, e) ->
      let elifs_core = List.map (fun (c', t') -> (broy_to_core c', broy_to_core t')) elifs in
      let rec desugar_ifs c t elifs e =   (* all arguments now term *)
        match elifs with [] -> e | (c', t') :: rest ->
          Lam ("cond", Universe 0, App (App (Var "if", c), Lam ("_", Universe 0, desugar_ifs c' t' rest e)))
      in desugar_ifs (broy_to_core c) (broy_to_core t) elifs_core (broy_to_core e)
  | BUnary (op, e) -> App (Var op, broy_to_core e)
  | BBinary (l, op, r) -> App (App (Var op, broy_to_core l), broy_to_core r)
  | BSection inner -> (match inner with
      | BElement (_typ, _id, e) -> broy_to_core e
      | BFunDefs (funs, e) ->
          List.fold_right (fun (f, body) acc -> Lam (f, Universe 0, acc)) funs (broy_to_core e)
      | _ -> Var "section")
  | BParens e -> broy_to_core e

(* ====================== TEST SUITE (now with proper context) ====================== *)
let test_ctx : context = [
  ("U0",   Universe 0);
  ("id",   Pi ("x", Universe 0, Universe 0));
  ("x",    Universe 0);
  ("cond", Universe 0);
  ("then", Universe 0);
  ("else", Universe 0);
  ("a",    Universe 0);
  ("b",    Universe 0);
]

let run_broy_test name broy_term expected =
  try
    let core = broy_to_core broy_term in
    let ty = infer test_ctx core in
    let norm_ty = normalize test_ctx ty in
    let norm_exp = normalize test_ctx expected in
    let passed = equal test_ctx norm_ty norm_exp in
    printf "Broy Test %s:\n  Term: %s\n  Inferred: %s\n  Expected: %s\n  Result: %s\n\n"
      name
      (string_of_term core)
      (string_of_term norm_ty)
      (string_of_term norm_exp)
      (if passed then "PASS" else "FAIL");
    passed
  with Failure msg ->
    printf "Broy Test %s FAILED: %s\n" name msg;
    false

(* Broy examples directly from your BNF *)
let sample_absfun   = BFunApp ("id", [])
let sample_section  = BSection (BElement ("U0", "x", BId "x"))
let sample_if       = BIf (BId "cond", BId "then", [], BId "else")
let sample_fct_add  = BFunApp ("id", [BId "a"; BId "b"])   (* FunApp example using known id *)

let () =
  printf "=== Broy Language (v0.0.1) ===\n\n";
  let all_passed =
    run_broy_test "AbsFun (id)" sample_absfun (Pi ("x", Universe 0, Universe 0)) &&
    run_broy_test "Section" sample_section (Universe 0) &&
    run_broy_test "If" sample_if (Universe 0) &&
    run_broy_test "FunctionDef / FunApp (id a b)" sample_fct_add (Universe 0)
  in
  if all_passed then printf "✅ All Broy tests passed!\n"
  else printf "❌ Some tests failed (see above).\n";
  printf "\nBroy language kernel (with Pi/Sigma extension) is ready.\n"
