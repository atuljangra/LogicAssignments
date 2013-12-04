type 'a set_c = 'a list;;

(*
  Assignment ) part 1
*)
let emptyset = [];;

(*
Running time: O(|S|)
S is the set and |S| is the cardinality of set.
*)
let rec member a lis = match lis with [] -> false
  | h::t -> if (h = a) then true else member a t;;

(*
Running time: O(|S|)
S is the set and |S| is the cardinality of set.
*)
let rec subseteq a b = match a with [] -> true
  | h::t -> if (member h b) then subseteq t b else false;;

(*
Running time: O(|S|)
S is the set and |S| is the cardinality of set.
*)
let rec setequal a b =
  if (subseteq a b) then if (subseteq b a) then true else false else false;;

(*
Running time: O(|S|)
S is the set and |S| is the cardinality of set.
*)
let rec union a b = match a with [] -> b
  | h::t -> if (member h b) then union t b else h::union t b;;

(*
Running time: O(|S|)
S is the set and |S| is the cardinality of set.
*)
let rec intersect a b = match a with [] -> []
  | h::t -> if (member h b) then h::intersect t b else intersect t b;;

(*
Running time: O(|S|)
S is the set and |S| is the cardinality of set.
*)
let rec difference a b = match a with [] -> []
| h::t -> if (member h b) then difference t b else h::difference t b;; 

(*
  Running time: O(|A|*|B|)
S is the set and |S| is the cardinality of set.
*)
let rec cartesian a b =
  let rec create_tuple elem lis = match lis with [] -> []
  | h::t -> [(elem, h)]@create_tuple elem t
  in
  match a with [] -> []
  | h::t -> (create_tuple h b)@cartesian t b;;
(*
  Running time: O(2^|A|)
*)
let rec power a =
  let rec internal_rec p q = match q with [] -> []
    | h::t -> [[p]@h]@internal_rec p t
  in
    match a with [] -> [[]]
    | h::t -> let pow = power t in pow @ internal_rec h pow;;


(*
  Assignment part 2
*)
(*  Identity relation.
    Takes a set A as input and returns a identity relation on A*A
*)
let rec identity a = match a with [] -> []
  | h::t -> [(h, h)]@identity t;;

(*  Relation Composition
    Takes two relations as inputs and return a relation which will be
    the relational composition of the two.
*)
let rec relComp a b =
  let rec helper (x, y) q = match q with [] -> []
    | (m,n)::t -> if (y=m) then [(x, n)] else (helper (x, y) t)
  in
  match a with [] -> []
    | h::t -> (helper h b)@(relComp t b);;
let set1 = [1;2;3;4;5;6;7;8;9;10];;
let set2 = [11;12;13;14;15;16;17;18;19;20];;
let set3 = [21;22;23;24;25;26;27;28;29;30];;
let relation1 = cartesian set1 set2;;
let relation2 = cartesian set2 set3;;
let relation3 = relComp relation1 relation2;;
let set4 = [2;4;7;3];;
let set5 = [3;5;8;7];;
let testRel = cartesian set4 set5;;
(*  Relation Inverse
    Takes a relation as input and return a relation which will be
    the relational inverse of the input relation.
*)
let rec relInv a = match a with [] -> []
  | (m, n)::t -> [(n, m)]@ relInv t;;

let rec relUnion a b =
  union a b;;

let rec relInter a b =
  intersect a b;;

let remove_elem e l =
  let rec go l acc = match l with
    | [] -> List.rev acc
    | x::xs when e = x -> go xs acc
    | x::xs -> go xs (x::acc)
  in go l []
   
(* A function to remove duplicates from the input set*)
let removeDup s =
  let rec helper l acc = match l with
    | [] -> List.rev acc
    | x::xs -> helper(remove_elem x xs) (x::acc)
  in
  helper s [];;
  
(* Gives the reflexive closure of the input relation *)
let reflexiveClosure r =
  let rec origSet r = match r with [] -> []
    | (a, b)::q -> [a]@(origSet q)
  in
  let setNoDups = removeDup (origSet r) in
  let rec iden r = match r with [] -> []
    | m::q -> [(m,m)]@(iden q)
  in
  let temp = iden setNoDups in
  relUnion r temp;;

(*Give the symmetric closure for the intput relation r *)
let symClosure r =
  relUnion r (relInv r);;

(* Returns the list of elements which are paired with input element elem in
the input relation rel *)
let rec find_neigh elem rel = match rel with [] -> []
  | (x, y)::tl -> if (elem = x) then [y]@(find_neigh elem tl) else find_neigh elem tl;;
    
(* Membership function of the transitive closure of the input relation *)
let transClosure (a, b) r =
  let rec memberTC q l1 l2 r =
    match l2 with [] -> false
    | h::t ->
      let neighList = find_neigh h r in
      let rec find_elem elem l =
        match l with [] -> false
        | hd::tl -> if (elem = hd) then true else find_elem elem tl
      in
      let rec merge lt1 lt2 lt3 =
        match lt3 with [] -> lt1
        | hd1::tl1 -> if ((find_elem hd1 lt1) ||(find_elem hd1 lt2))
          then merge lt1 lt2 tl1  else (merge lt1 lt2 tl1)@[hd1]
      in
      if neighList = [] then
        if t = [] then false
        else memberTC q l1 t r
      else
        if (find_elem q neighList) then true
        else
          let temp_list = merge t l1 neighList in
          memberTC q (h::l1) (temp_list) r
        in
  memberTC b [] [a] r;;

(* Tells whether (a, b)is an element in the input relation *)
let memberClosure (a, b) r =
  let rec find (x, y) rel = match rel with [] -> false
    | (a, b)::tl -> if ( a = x && b = y) then true else find (x, y) tl
  in
  find (a, b) r;;

(* Membership function for reflexive transitive closure of the input relation *)
let refTranClosure (a, b) r =
  let refClo = reflexiveClosure r in
  let val1 = memberClosure (a, b) refClo in
  let val2 = transClosure (a, b) r in
  val1 || val2;;

(* Membership function for equivalence closure of the input relation *)
let equivalence (a, b) r =
  let symClo = symClosure r in
  let val1 = memberClosure (a, b) symClo in
  let val2 = refTranClosure (a, b) r in
  val1 || val2;;
(*
let relation4 = symClosure relation1;;
let relation5 = reflexiveClosure relation2;;
*)
let testRel = [(2, 3); (4, 5); (7, 8); (3, 7)];
