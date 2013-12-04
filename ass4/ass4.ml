type symbol = Const of string
  | Func of string * int;;

type term =
  | Constant of string
  | Variable of string
  | Function of string * term list;;

type formula = True
  | False
  | Term of term
  | And of formula *  formula
  | Or of formula * formula
  | Imply of formula * formula
  | Equiv of formula * formula
  | Negation of formula
  | ForAll of string * formula
  | ThereExists of string * formula;;

(* constructors.                                  *)

let mk_and p q = And(p,q) and mk_or p q = Or(p,q)
and mk_imp p q = Imply(p,q) and mk_eqv p q = Equiv(p,q)
and mk_forall x p = ForAll(x,p) and mk_exists x p = ThereExists(x,p);;


(*  Telling if a formula is well formed or not*)
let rec wff phi sigma var pi =
  let helper x y =
    match (x, y) with
    | (Const a, Const b) -> b = a
    | (Func (a, i), Func (b, j))  ->  a = b && i = j
    | (_, _)  ->  false

  in
    let rec sechelper ter =
      match ter with
      | Constant a  -> List.exists (fun x -> helper x (Const a)) sigma
      | Variable a  -> List.exists (fun x -> helper x (Const a)) var
      | Function (a, l) ->
      (List.exists(fun x -> helper (Func (a, List.length l)) x) sigma)
        && List.fold_left (fun x y -> x && (sechelper y)) true l
  in
    match phi with
      | True -> true
      | False -> true
      | Term t -> sechelper t
      | And (a, b) -> (wff a sigma var pi) && (wff b sigma var pi)
      | Or (a, b) -> (wff a sigma var pi) && (wff b sigma var pi)
      | Imply (a, b) -> (wff a sigma var pi) && (wff b sigma var pi)
      | Equiv (a, b) -> (wff a sigma var pi) && (wff b sigma var pi)
      | Negation (a)  ->  (wff a sigma var pi)
      | ForAll(x, a)  -> (List.exists(fun v -> v = (Const x)) var) && (wff a sigma var pi)
      | ThereExists(x, a) -> (List.exists(fun v -> v = (Const x)) var) && (wff a sigma var pi);;

(* Examples *)
let term1 = Function ("a", [Function ("a", [Variable "x" ;Variable "y";Variable "z"; Constant "s"])]);;
let form1 = Negation (Term term1);;

let form2 = And(ForAll ("x", True), True);;

(*Quan in Or in Or *)
let form3 = Or(Or(ForAll ("x", True), True), True);;

let form4 = And(And(ThereExists ("x", And (Term (Variable "x"), Term (Variable "y"))), True), True);;

let form5 = Or(Imply(ForAll ("x", True), True), True);;

let test = Imply(
                  Or( True, (ThereExists("x", True) )),
                    (ForAll("z", True)));;
(* Term Size (tree size?) *)
let rec treesize ter =
  match ter with
    | Function (a, l) -> List.fold_left (fun x y -> x + treesize y) 0 l
    | _ -> 1;;
    
(* Formula Size *)
let rec fsize phi =
    match phi with
    | True -> 1
    | False -> 1
    | Term t -> treesize t
    | And (a, b) -> fsize(a) + fsize(b)
    | Or (a, b) -> fsize(a) + fsize(b)
    | Imply (a, b) -> fsize(a) + fsize(b)
    | Equiv (a, b) -> fsize(a) + fsize(b)
    | Negation a  -> fsize a
    | ForAll(x, a)  -> fsize a
    | ThereExists(x, a) -> fsize a;;

(* Max *)
let max a b = if (a > b) then a else b;;

(*Term Height*)
let rec treeht ter =
  match ter with
  | Function (a, l) -> 1 + List.fold_left (fun x y -> max x (treeht y)) 0 l
  | _ -> 1;;

(* Formula height *)
let rec fht phi =
  match phi with
    | True -> 1
    | False -> 1
    | Term t  -> 1 + treeht t
    | And (a, b) -> 1 + max (fht a) (fht b)
    | Or (a, b) -> 1 + max (fht a) (fht b)
    | Imply (a, b) -> 1 + max (fht a) (fht b)
    | Equiv (a, b) -> 1 + max (fht a) (fht b)
    | Negation a  -> fht a
    | ForAll(x, a)  -> fht a
    | ThereExists(x, a) -> fht a;;

(*Function to list the set of free variables in a formula *)
let rec listFreeVar phi =
  let rec helper ter =
    match ter with
    | Function (a, l) -> List.fold_left (fun l1 l2 -> l1 @ (helper l2)) [] l
    | Variable a -> [Variable a]
    | _ -> []
  in
  let rec remHelper a lis =
    match lis with
    | [] -> []
    | h :: hs -> if a = h then remHelper a hs
    else h::(remHelper a hs)
  in
  match phi with
    | True -> []
    | False -> []
    | Term t  -> helper t
    | ForAll(x, a)  -> remHelper (Variable x) (listFreeVar a)
    | ThereExists(x, a) -> remHelper (Variable x) (listFreeVar a)
    | And (a, b) -> (listFreeVar a) @ (listFreeVar b)
    | Or (a, b) -> (listFreeVar a) @ (listFreeVar b)
    | Imply (a, b) -> (listFreeVar a) @ (listFreeVar b)
    | Equiv (a, b) -> (listFreeVar a) @ (listFreeVar b)
    | Negation a  -> listFreeVar a;;

(* Converting the formula into nnf form *)
let rec nnf phi =
  match phi with
  | And (a, b) ->  And(nnf a, nnf b)
  | Or (a, b) ->  Or(nnf a, nnf b)
  | Imply (a, b) ->  Or(nnf (Negation a), nnf b)
  | Equiv (a, b) ->  Or(And(nnf a, nnf b), And(nnf (Negation a), nnf (Negation b)))  
  | Negation(Negation a) -> nnf a
  | Negation (And (a, b)) -> Or(nnf (Negation a), nnf (Negation b))
  | Negation (Or (a, b)) -> And(nnf (Negation a), nnf (Negation b))
  | Negation (Imply (a, b)) -> And(nnf a, nnf (Negation b))
  | Negation (Equiv (a, b)) ->
      Or(And(nnf a, nnf (Negation b)), And(nnf (Negation a), nnf b))
  | ForAll(x, a) -> ForAll(x, nnf a)
  | ThereExists(x, a) -> ThereExists(x, nnf a)
  | Negation(ForAll(x, a)) -> ThereExists(x, nnf (Negation a))
  | Negation(ThereExists(x, a)) -> ForAll(x, nnf (Negation a))
  | _ -> phi;;

(* converts a given formula (sentence) into prenex normal form. *)

(* Substitution in formula with variable renaming *)
let rec termsubst t y x =
  let rec helper l =
    match l with [] -> []
    | Variable(h)::hs -> if (h = x) then Variable(y)::(helper hs)
          else Variable(h)::(helper hs)
    | h::hs -> h::(helper hs)
  in
  match t with
    | Function (a, ls) -> Function(a, (helper ls)) 
    | Variable z -> if x = z then Variable y else Variable z;;


let rec subst phi y x =
  match phi with
    | True -> True
    | False -> False
    | Term t -> Term (termsubst t y x)
    | Negation a -> Negation (subst a y x)
    | And (a, b)  -> And((subst a y x), (subst b y x))
    | Or (a, b)  -> Or((subst a y x), (subst b y x))
    | Imply (a, b)  -> Imply((subst a y x), (subst b y x))
    | Equiv (a, b)  -> Equiv((subst a y x), (subst b y x))
    | ForAll (z, a) -> if (z = x) then ForAll(y, (subst a y x))
        else ForAll(z, (subst a y x))
    | ThereExists (z, a) -> if (z = x) then ThereExists(y, (subst a y x))
        else ThereExists(z, (subst a y x));;

let rec createFunction t y x = 
  let rec helper l = 
    match l with [] -> []
      | Variable(h)::hs -> if (h = y) then (Function ("y", [Variable
      "x"]))::(helper hs)
      else Variable(h)::(helper hs)
      | h::hs -> h::(helper hs)
  
      in
  match t with 
  | Function (a, ls) -> Function (a, helper ls)
  | Variable z -> if z = y then Variable x else Variable z;;


 let rec xOsubst phi y x =
  match phi with
    | True -> True
    | False -> False
    | Term t -> Term (createFunction t y x)
    | Negation a -> Negation (xOsubst a y x)
    | And (a, b)  -> And((xOsubst a y x), (xOsubst b y x))
    | Or (a, b)  -> Or((xOsubst a y x), (xOsubst b y x))
    | Imply (a, b)  -> Imply((xOsubst a y x), (xOsubst b y x))
    | Equiv (a, b)  -> Equiv((xOsubst a y x), (xOsubst b y x))
    | ForAll (z, a) -> if (z = x) then ForAll(y, (xOsubst a y x))
        else ForAll(z, (xOsubst a y x))
    | ThereExists (z, a) -> if (z = x) then ThereExists(y, (xOsubst a y x))
        else ThereExists(z, (xOsubst a y x));;   
let rec negationPrenexHelper p =
  match p with
    | ForAll (x, y) -> ThereExists(x, (negationPrenexHelper y))
    | ThereExists (x, y) -> ForAll(x, (negationPrenexHelper y))
    | True -> False
    | False -> True
    | _ -> negationPrenexHelper p;;


let rec countQuantifiers phi =
  match phi with
    | ForAll (_, a) -> 1 + (countQuantifiers a)
    | ThereExists (_, a) -> 1 + (countQuantifiers a)
    | _ -> 0;;

let rec prenexHelper phi n =
  match phi with
    | True -> True
    | False -> False
    | Term t -> Term t
    | ForAll (x, a) ->
        let str = "x"^string_of_int n;
        in
          ForAll(str, prenexHelper (subst a str x) (n+1))
    | ThereExists(x, a) ->
      let str = "x"^string_of_int n;
      in
        ThereExists(str, prenexHelper (subst a str x) (n+1))
    | Negation a ->
      let pre = (prenexHelper a n)
        in negationPrenexHelper pre
    | Or(a, b) ->
        let preA = (prenexHelper a n) in
        let quanNo = countQuantifiers preA in
        let preB = (prenexHelper b (n+quanNo)) in
        let rec pullOut(Or(a, b)) = match a with
            | ForAll (x, preA) -> ForAll(x, pullOut(Or(preA, b))) 
            | ThereExists (x, preA) -> ThereExists(x, pullOut(Or(preA, b)))
            | _ -> match b with
              | ForAll (x, preA) -> ForAll(x, pullOut(Or(a, preA))) 
              | ThereExists (x, preA) -> ThereExists(x, pullOut(Or(preA, a)))
              | _ -> Or(a, b)
        in
        pullOut(Or(preA, preB))
    | And(a, b) ->
        let preA = (prenexHelper a n) in
        let quanNo = countQuantifiers preA in
        let preB = (prenexHelper b (n+quanNo)) in
        let rec pullOut(And(a, b)) = match a with
            | ForAll (x, preA) -> ForAll(x, pullOut(And(preA, b))) 
            | ThereExists (x, preA) -> ThereExists(x, pullOut(And(preA, b)))
            | _ -> match b with
              | ForAll (x , preA) -> ForAll(x, pullOut(And(a, preA))) 
              | ThereExists (x, preA) -> ThereExists(x, pullOut(And(preA, a)))
              | _ -> And(a, b)
        in
        pullOut(And(preA, preB))
    | _ -> phi;;

let prenex phi = prenexHelper (nnf phi) 0;;

let something = And (Negation True, ThereExists ("x", Negation True));;
let something = ForAll ("x", (
                    ThereExists("y", (
                        ForAll ("z", (
                          ThereExists ("w",(Term (Function ("a", [Variable "x";
                          Variable "y"; Variable "z"; Variable "w";])))
                          ))
                        ))
                    ))
);;
(* function skolemize that converts a prenex form formula into 
a skolemized form where there are no existentially quantified variables.*)

(* Formula Size *)
let rec prenexLength phi =
    match phi with
    | True -> 0
    | False -> 0
    | Term t -> 0
    | And (a, b) -> prenexLength(a) + prenexLength(b)
    | Or (a, b) -> prenexLength(a) + prenexLength(b)
    | Imply (a, b) -> prenexLength(a) + prenexLength(b)
    | Equiv (a, b) -> prenexLength(a) + prenexLength(b)
    | Negation a  -> prenexLength a
    | ForAll(x, a)  -> 1 + prenexLength a
    | ThereExists(x, a) -> 1 + prenexLength a;;

(* Some problem with the Term *)
let rec skolemize phi =
  let rec iterBefore phi x = match phi with 
    | ThereExists(x, a) -> Term (Variable "x")
    | ForAll (y, a) -> Term (Function ("x", [Variable "y"]))
    | _ -> Term (Variable "x")
  in 
  match phi with
    (*  We need a unique number to append after c(Constant), thus calculating the
        prenex length and appening it *)
    | ThereExists(y, a) -> skolemize(( xOsubst a y "x"))
    | ForAll (x, a) ->  ForAll (x, skolemize(a))
    | Negation a -> Negation (skolemize a)
    | And (a, b) -> And ((skolemize a), (skolemize b))
    | Or (a, b) -> Or ((skolemize a), (skolemize b))
    | _ -> phi;;

let form6 = Or(And((subst form1 "y0" "y"), (subst form4 "x0" "x")), And((subst form3 "x1" "x"), (subst form2 "x2" "x")));;

let form7 = Or(And(ForAll ("x", True), True), True);;

(* takes a skolem-form formula and converts its 
"matrix" into CNF (Product of Sums) clausal form. *)
(* This functions pushes all the disjunctions inside *)
let rec pushDisjunction phi = match phi with True -> True
  | False -> False
  | Term a -> Term a
  | Or (And(a, b), And(c, d)) -> And(And(pushDisjunction(Or(a, c)),
        pushDisjunction(Or(b, c))), And(pushDisjunction(Or(a, d)),
        pushDisjunction(Or(b, d))))
  | Or (a, And(b, c)) -> And(pushDisjunction(Or(a, b)), pushDisjunction(Or(a, c)))
  | Or (And(a, b), c) -> And(pushDisjunction(Or(a, c)), pushDisjunction(Or(b, c)))
  | Or (a, b) -> Or (pushDisjunction(a), pushDisjunction(b))
  | And (a, b) -> And (pushDisjunction(a), pushDisjunction(b))
  | Negation(a) -> Negation(pushDisjunction(a))
  | _ -> phi;;

let isAnd p = match p with And(a, b) -> true
  | p -> false;;

(* Check if there is 'and' inside 'or'*)
let rec andInOr p = match p with True -> false
  | False -> false
  | Term t -> false
  | Or (a, b) -> if (isAnd(a) || isAnd(b)) then true else (andInOr a) || (andInOr b)
  | And (a, b) -> andInOr(a) || andInOr(b)
  | ForAll(x, a) -> andInOr(a)
  | ThereExists (x, a) -> andInOr(a)
  | Negation (a) -> andInOr(a);;

let rec cnf_helper p = if (andInOr p) then (cnf_helper (pushDisjunction(nnf p))) else p;;
(* CNF form of a given proposition *)
let rec cnf p = cnf_helper (pushDisjunction(nnf p));;
(* Above working, example is cnf form7*)

(*Resolution of the clauses *)

