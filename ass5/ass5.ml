type binaryoperator = And
  | Or
  | Imply
  | Equiv
  | Ineq;;

type 'a proposition = True
  | False
  | Letter of 'a
  | BinaryOp of binaryoperator*('a proposition)*('a proposition)
  | Negation of 'a proposition;;

type 'a sequent = Seq of ('a proposition list) * ('a proposition);;

type 'a constructor =
  | Nil
  | Hyp
  | ImplyIntro of 'a rule
  | ImplyElim of ('a rule) * ('a rule)
  | AndElim of 'a rule
  | AndIntro of ('a rule) * ('a rule)
  | OrIntro of 'a rule
  | OrElem of ('a rule) * ('a rule) * ('a rule)
  | NegIntro of 'a rule
  | NegElim of 'a rule
  and
  'a rule = ('a sequent) * ('a constructor);;

let rec belongs phi delta =
  if phi=True then true
  else
    let rec helper delta =
      match delta with
      | [] -> false;
      | h::hs -> if h=phi then true else helper hs

  in
  helper delta;;

let rec wfndp candidate =
  match candidate with
  | (Seq (_, _), Nil) -> true
  | (Seq (phi, delta), Hyp) -> (belongs delta phi)
  | (Seq (phi, BinaryOp (Imply, a, b)), ImplyIntro r) ->
    let helper r = match r with
      | (Seq (d, q), _) -> (d=phi@[a]) &&(b=q) && (wfndp r)
    in
    helper r
  | (Seq (phi, delta), ImplyElim (r1, r2)) ->
    let helper r1 r2 = match (r1, r2) with
      | ((Seq (d1, BinaryOp(Imply, a, b)), _), (Seq (d2, q1), _)) ->
        (phi=d1) && (phi=d2) && (delta=b) && (a=q1) && (wfndp r1) && (wfndp r2)
      | _ -> false
    in
      helper r1 r2
  | (Seq (d1, BinaryOp(And, q1, q2)), AndIntro (r1, r2)) ->
    let helper r1 r2 = match (r1, r2) with
      | ((Seq (d11, q11), _), (Seq (d12, q12), _)) -> (d1=d11) && (d1=d12)
        && (q1=q11) && (q2=q12) && (wfndp r1) && (wfndp r2)
    in
      helper r1 r2
  | (Seq (d1, q1), AndElim r) ->
    let helper r =  match r with
      | (Seq (d11, BinaryOp(And, q11, q12)), _) -> d1=d11 && (q1=q11 || q1=q12)
        && wfndp r
      | _ -> false
    in
      helper r
  | (Seq (d1, BinaryOp (Or, q1, q2)), OrIntro r) ->
    let helper r = match r with
      | (Seq (d11, q3), _ ) -> (q3=q1 || q3=q2) && d1=d11 && wfndp r
    in
      helper r
  | (Seq (d1, sii), OrElem(r1, r2, r3)) ->
    let helper r1 r2 r3 = match (r1, r2, r3) with
      | ((Seq(d11, BinaryOp (Or, q1, q2)), _), (Seq(d2, sii1), _), (Seq (d3, sii2), _)) ->
      sii=sii1 && sii=sii2 && d1=d11 && (d2=d1@[q1]) && (d3=d1@[q2]) && (wfndp r1)  && (wfndp r2)  && (wfndp r3)
      | _ -> false
    in
      helper r1 r2 r3
  | (Seq (d1, Negation q1), NegIntro r) ->
    let helper r = match r with
      | (Seq (d2, False), _ ) -> (d2=d1@[q1]) && wfndp r
      | _ -> false
    in
      helper r
  | (Seq (d1, q1), NegElim r) ->
    let helper r = match r with
      | (Seq (d2, False), _ ) -> (d2=d1@[q1]) && wfndp r
      | _ -> false
    in
      helper r
  | _ -> false;;


let p = Letter 'p';;
let q = Letter 'q';;
let r = Letter 'r';;
let tree1 = (Seq([], BinaryOp (And, p, q))
            , AndIntro ( (Seq ([], q), Nil) , (Seq([], q), Nil) ));;  
let tree2 = (Seq([], BinaryOp (And, p, q))
            , AndIntro ( (Seq ([p], p), Nil) , (Seq([], q), Nil) ));;  
let tree3 = (Seq([], p)
            , AndElim ( (Seq ([], BinaryOp(And, p, r)), Nil) ));; 
let tree4 = (Seq ([], q), ImplyElim ((Seq ([], BinaryOp(Imply, p, q)), Nil), (Seq([], p)
            , AndElim ( (Seq ([], BinaryOp(And, p, r)), Nil) ))
));;


