(* Type declaration for our proposition *)
type variable = char;;

type proposition = False
  | True
  | Var of variable
  | Not of proposition
  | And of proposition*proposition
  | Or of proposition*proposition
  | Implies of proposition*proposition
  | Iff of proposition*proposition
  | Xor of proposition*proposition;;

(* representation for TruthAssignments or Valuations *) 
let rho = [('a', true); ('b', false); ('c', true); ('d', false); ('e', true);
('f', false); ('g', true); ('h', false); ('q', true); ('p', false)];;

(* Some test propositions to check the correctness of the designed functions *)
let prop1 = Not False;;
let prop2 = And (Var 'a', Or(Var 'c', Var 'd'));;
let prop3 = And (Var 'a', Or(Var 'c', Implies(True, True)));;
let prop4 = Or (Var 'a', And(Var 'c', Implies(True, True)));;
let prop5 = Implies(Iff(And(Var 'c', Not(Var 'b')), (Or(Xor(Var 'a', Var 'd'), Var 'c'))), (Or (Var 'a', And(Var 'c', Implies(True, True)))));;
let prop6 = Or(Or(Or( And (Var 'a', Var 'b'), And (Var 'c', Var 'd')), And (Var 'e', Var 'f')), And(Var 'g', Var 'h'));;
let prop7 = Or(Or( And (Var 'a', Var 'b'), And (Var 'c', Var 'd')), Or( And (Var 'e', Var 'f'), And (Var 'g', Var 'h')));;
let prop8 = Or(Or(And(Var 'a', Var 'b'), And(Var 'c', Var 'd')), And(Var 'e', Var 'f'));;
let prop10 =  Or(Or(Or( And (Var 'a', Var 'b'), And (Var 'c', Var 'd')), Or( And (Var 'e', Var 'f'),
              And (Var 'g', Var 'h'))), Or(Or(And(Var 'a', Var 'b'), And(Var 'c', Var 'd')), And(Var 'e', Var 'f')));;
let test = Implies(Not(Var 'p'), Not(Var 'q'));;
let diff = Implies(Var 'q', Var 'p');;
let imp = Implies(test, diff);;
(* Size of a proposition *)
let rec size p = match p with True -> 1
  | False -> 1
  | Var a -> 1
  | Not(a) -> 1 + size(a)
  | And(a, b) -> 1 + size(a) + size(b)
  | Or(a, b) -> 1 + size(a) + size(b)
  | Implies(a, b) -> 1 + size(a) + size(b)
  | Iff(a, b) -> 1 + size(a) + size(b)
  | Xor(a, b) -> 1 + size(a) + size(b);;

(* Helper for height *)
let max a b = if (a < b) then b else a;;

(* Height of a proposition *)
let rec ht p = match p with True -> 1
  | False -> 1
  | Var a -> 1
  | Not(a) -> 1 + ht(a)
  | And(a, b) -> 1 + (max (ht a) (ht b))
  | Or(a, b) -> 1 + (max (ht a) (ht b))
  | Implies(a, b) -> 1 + (max (ht a) (ht b))
  | Iff(a, b) -> 1 + (max (ht a) (ht b))
  | Xor(a, b) -> 1 + (max (ht a) (ht b));;

(* Returns a list containing the letters on a proposition *)
let rec letters p = match p with True -> []
  | False -> []
  | Var a -> [a]
  | Not(a) -> letters a
  | And(a, b) -> letters a @ letters b
  | Or(a, b) -> letters a @ letters b
  | Implies(a, b) -> letters a @ letters b
  | Iff(a, b) -> letters a @ letters b
  | Xor(a, b) -> letters a @ letters b;;

(* Helper function which gets the value of a Var from the rho
If the variable is not in the rho, then we raise an exeption *)
exception VarNotFoundInRhoException;;
let rec value a rho = match rho with
  (m, n)::q -> if(a =m) then n else value a q
  | [] -> raise VarNotFoundInRhoException;;
(* The truth function as a recursive function, given a proposition  
and a truthAssignment*)
let rec truthVal a rho = match a with True -> true
  | False -> false
  | Var a -> value a rho
  | Not(a) -> if(truthVal a rho) then false else true
  | And(a, b) -> (truthVal a rho) && (truthVal b rho)
  | Or(a, b) -> (truthVal a rho) || (truthVal b rho)
  | Implies(a, b) -> if ((truthVal a rho) = false) then true else (truthVal b rho) 
  | Iff(a, b) -> if ((truthVal a rho) = (truthVal b rho)) then true else false
  | Xor(a, b) -> if ((truthVal a rho) = (truthVal b rho)) then false else true;;

(* NNf form of a given proposition *)
let rec nnf p = match p with True -> nnf(Not (False))
  | False -> False
  | Var a -> Var a
  | Not(a) -> helper a
  | And(a, b) -> And( nnf a, nnf b)
  | Or(a, b) -> Or(nnf a, nnf b)
  | Implies(a, b) -> nnf (Or(Not(a), b))
  | Iff(a, b) -> nnf (And(Implies(a, b), Implies(b, a)))
  | Xor (a, b) -> nnf (Not(Iff(a, b)))
  and
  helper p = match p with False -> Not( False)
  | True -> False
  | Var a -> Not( Var a)
  | Not a -> nnf p
  | And(a, b) -> Or ((nnf(Not a)), (nnf (Not b)))
  | Or (a, b) -> And ((nnf (Not a)),(nnf (Not b)))
  | Implies(a, b) -> nnf (And(a, Not(b)));
  | Iff(a, b) -> nnf (Or ((Implies(Not a, Not b)), (Implies(Not b, Not a))))
  | Xor(a, b) -> helper(Iff(a, b));;

(* NNf form of a given proposition *)
let rec nnf_dummy p = match p with True -> True
  | False -> False
  | Var a -> Var a
  | Not(a) -> helper_dummy a
  | And(a, b) -> And( nnf_dummy a, nnf_dummy b)
  | Or(a, b) -> Or(nnf_dummy a, nnf_dummy b)
  | Implies(a, b) -> nnf_dummy (Or(Not(a), b))
  | Iff(a, b) -> nnf_dummy (And(Implies(a, b), Implies(b, a)))
  | Xor (a, b) -> nnf_dummy (Not(Iff(a, b)))
  and
  helper_dummy p = match p with False -> True
  | True -> False
  | Var a -> Not( Var a)
  | Not a -> nnf_dummy p
  | And(a, b) -> Or ((nnf_dummy(Not a)), (nnf_dummy (Not b)))
  | Or (a, b) -> And ((nnf_dummy (Not a)),(nnf_dummy (Not b)))
  | Implies(a, b) -> nnf_dummy (And(a, Not(b)));
  | Iff(a, b) -> nnf_dummy (Or ((Implies(Not a, Not b)), (Implies(Not b, Not a))))
  | Xor(a, b) -> helper_dummy(Iff(a, b));;

(* This functions pushes all the disjunctions inside *)
let rec pushDisjunction p = match p with True -> True
  | False -> False
  | Var a -> Var a
  | Or (And(a, b), And(c, d)) -> And(And(pushDisjunction(Or(a, c)), pushDisjunction(Or(b, c))), And(pushDisjunction(Or(a, d)), pushDisjunction(Or(b, d))))
  | Or (a, And(b, c)) -> And(pushDisjunction(Or(a, b)), pushDisjunction(Or(a, c)))
  | Or (And(a, b), c) -> And(pushDisjunction(Or(a, c)), pushDisjunction(Or(b, c)))
  | Or (a, b) -> Or (pushDisjunction(a), pushDisjunction(b))
  | And (a, b) -> And (pushDisjunction(a), pushDisjunction(b))
  | Not(a) -> Not(pushDisjunction(a));;
  
let isAnd p = match p with And(a, b) -> true
  | p -> false;;
(* Check if there is 'and' inside 'or'*)
let rec andInOr p = match p with True -> false
  | False -> false
  | Var a -> false
  | Not a -> false
  | Or (a, b) -> if (isAnd(a) || isAnd(b)) then true else (andInOr a) || (andInOr b)
  | And (a, b) -> andInOr(a) || andInOr(b);;


let rec cnf_w p = if (andInOr p) then (cnf_w (pushDisjunction(nnf_dummy p))) else p;;
(* CNF form of a given proposition *)
let rec cnf p = cnf_w (pushDisjunction(nnf_dummy p));;

(* This function pushes all the conjunctions insde *)
let rec pushConjuction p = match p with True -> True
  | False -> False
  | Var a -> Var a
  | And(Or(a, b), c) -> Or(pushConjuction(And(a, c)), pushConjuction(And(b, c)))
  | And(a, Or(b, c)) -> Or(pushConjuction(And(a, b)), pushConjuction(And(a, c)))
  | And(a, b) -> And(pushConjuction(a), pushConjuction(b))
  | Or(a, b) -> Or(pushConjuction(a), pushConjuction(b))
  | Not (a) -> Not(pushConjuction(a));;

let isOr p = match p with Or(a, b) -> true
  | p -> false;;

let rec orInAnd p = match p with True -> false
  | False -> false
  | Var a -> false
  | Not a -> false
  | And(a, b) -> if(isOr(a) || isOr(b)) then true else (orInAnd a) || (orInAnd b)
  | Or(a, b) -> orInAnd(a) || orInAnd(b);;

let rec dnf_w p = if (orInAnd p) then (dnf_w (pushConjuction(nnf_dummy p))) else p;;

(* DNF form of a given proposition *)
let rec dnf p = dnf_w(pushConjuction(nnf_dummy p));;

(*  Returns true if the truth value of a and b are equal with respect to the
    rho truth assignment *)
let areEqual a b rho = if( (truthVal a rho) = (truthVal b rho)) then true else false;

(* For exponential blowup, use prop8 and prop 10 *) 
