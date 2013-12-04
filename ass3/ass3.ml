type binaryOperators = And
  | Or
  | Imply
  | Equiv
  | Ineq;;

type unaryOperator = Neg;;

type 'a proposition = True
  | False
  | Letter of 'a
  | BinaryOp of binaryOperators*('a proposition)*('a proposition)
  | UnaryOp of unaryOperator*('a proposition);;

let applyUnaryOp op a =
  match op with
  | Neg -> not a;;

let rec applyBinaryOp op a b =
  match op with
  | And -> a && b
  | Or -> a || b
  | Equiv -> a = b
  | Imply -> applyBinaryOp Or (applyUnaryOp Neg a) b
  | Ineq -> not (a = b)

let rec truth p v = 
  match p with 
  | True -> true
  | False -> false
  | Letter a -> v a
  | BinaryOp (op,p1,p2) -> applyBinaryOp op (truth p1 v) (truth p2 v)
  | UnaryOp (op,p1) -> applyUnaryOp op (truth p1 v);;

let rec substitution p (x,b) = 
  match p with 
  | True -> True
  | False -> False
  | Letter a -> 
    if a=x 
    then b
    else Letter a
  | BinaryOp (op,p1,p2) -> BinaryOp (op,substitution p1 (x,b), substitution p2 (x,b))
  | UnaryOp (op,p1) -> UnaryOp (op,substitution p1 (x,b))

let initT n = 
  let t = Hashtbl.create 2
  in
    let _ = Hashtbl.add t 0 (n+1,n,n)
    and _ = Hashtbl.add t 1 (n+1,n,n)
    in
      t;;

let initH n = 
  let t = Hashtbl.create 1
  in
    t;;

let addT t (i,l,h) =
  let len = Hashtbl.length t
  in
  let _ = Hashtbl.add t len (i,l,h)
  in
  len;;

let addH t (i,l,h) u = 
  let _ = Printf.printf "i: %d low: %d high %d \t u: %d \n" i l h u;
  and _ = flush stdout
  in
  Hashtbl.add t (i,l,h) u;;

let make t ht (i,l,h) = 
  if l=h
    then 
      (* let _ = Printf.printf "i: %d low: %d high %d \n" i l h;
      and _ = flush stdout;
      in 
      *)l
  else if Hashtbl.mem ht (i,l,h)
    then Hashtbl.find ht (i,l,h)
  else
    (*let _ = Printf.printf "i:%d " i; Printf.printf "LOW:%d " l; Printf.printf "high: %d \n" h;
    and _ = flush stdout
    in 
    *)let u = addT t (i,l,h)
    in
    let _ = addH ht (i,l,h) u
    in
    u;;

(*
let print ht root = 
  if Hashtbl.mem ht root
  then 
    let a = Hashtbl.find ht root
    in 
    let _ = Printf.printf "%d %d %d \n" a
    and _ = flush stdout
in ;;
  *)
let build t h p n =
  let rec build2 p i =
   if i > n
    then match (truth p (fun x -> true)) with
    | false ->
      (*  let _ = Printf.printf "::0:: \n";
        and _ = flush stdout;
      in*)
        0
    | true ->
        (*let _ = Printf.printf "::1:: \n";
        and _ = flush stdout;
      in  *)
        1
      else
      let v0 = build2 (substitution p (i,False)) (i+1)
      and v1 = build2 (substitution p (i,True)) (i+1)
      in
        make t h (i,v0,v1)
  in
    build2 p 1;;

let applyOperator op u1 u2 = 
  let (t1,t2) = 
    match (u1,u2) with 
    | (0,0) -> (false,false)
    | (0,1) -> (false,true)
    | (1,0) -> (true,false)
    | (1,1) -> (true,true)
    | (_,_) -> failwith "invalid arg"
  in
    match applyBinaryOp op t1 t2 with
    | false -> 0
    | true -> 1;;

let apply t h (op,n1,n2) = 
  let g = Hashtbl.create 1
  in
    let rec helper u1 u2 = 
      if Hashtbl.mem g (u1,u2) 
        then Hashtbl.find g (u1,u2)
      else if (u1<2 && u2<2)
        then let u = applyOperator op u1 u2
        in
          let _ = Hashtbl.add g (u1,u2) u
          in
          u
      else 
        let (i1,l1,h1) = Hashtbl.find t u1
        and (i2,l2,h2) = Hashtbl.find t u2
        in
          if i1=i2 then 
            let u = make t h (i1, (helper l1 l2), (helper h1 h2))
            in
              let _ = Hashtbl.add g (u1,u2) u
              in
                u
          else if i1 < i2 then 
            let u = make t h (i1, (helper l1 u2), (helper h1 u2))
            in
              let _ = Hashtbl.add g (u1,u2) u
              in
              u
            else 
              let u = make t h (i2, (helper l2 u1), (helper h2 u1))
              in
              let _ = Hashtbl.add g (u1,u2) u
              in
              u
    in
      helper n1 n2;;

let taut1 = BinaryOp(Or,Letter 1, UnaryOp(Neg,Letter 1));;
let taut2 = BinaryOp(Imply,Letter 1, Letter 1);;
let p1 = BinaryOp(Imply,Letter 1, Letter 2);;
let p2 = BinaryOp(Or,UnaryOp(Neg,Letter 1),Letter 2);;
let con1 = BinaryOp(And,Letter 1, UnaryOp(Neg,Letter 1));;
let test = BinaryOp(Imply, Letter 1, Letter 2);;
let diff = BinaryOp(Imply, UnaryOp(Neg, Letter 2), UnaryOp(Neg, Letter 1));; 
let imp = BinaryOp(Imply, test, diff);;
let testTaut2 =
  let t = (initT 4)
  and h = initH 4
  in
  build t h taut2 2;;

let testTaut1 =
  let t = (initT 4)
  and h = initH 4
  in build t h taut1 2;;

let testP1 =
  let t = (initT 4)
  and h = initH 4
  in build t h con1 2;;

let testP2 =
  let t = (initT 4)
  and h = initH 4
  in build t h diff 4;;

let testcon =
  let t = (initT 4)
  and h = initH 4
  in build t h test 4;;

let testImp =
  let t = (initT 4)
  and h = initH 4
  in build t h imp 3 ;;
                         
let winningMoves = 
  let wh1 = BinaryOp(And,BinaryOp(Equiv,Letter 1, Letter 2),
            BinaryOp(Equiv,Letter 2,Letter 3))
  and wh2 = BinaryOp(And,BinaryOp(Equiv,Letter 4, Letter 5),
            BinaryOp(Equiv,Letter 5,Letter 6))
  and wh3 = BinaryOp(And,BinaryOp(Equiv,Letter 7, Letter 8),
            BinaryOp(Equiv,Letter 8,Letter 9))
  and wv1 = BinaryOp(And,BinaryOp(Equiv,Letter 1, Letter 4),
            BinaryOp(Equiv,Letter 4,Letter 7))
  and wv2 = BinaryOp(And,BinaryOp(Equiv,Letter 2, Letter 5),
            BinaryOp(Equiv,Letter 5,Letter 8))
  and wv3 = BinaryOp(And,BinaryOp(Equiv,Letter 3, Letter 6),
            BinaryOp(Equiv,Letter 6,Letter 9))
  and wd1 = BinaryOp(And,BinaryOp(Equiv,Letter 1, Letter 5),
            BinaryOp(Equiv,Letter 5,Letter 9))
  and wd2 = BinaryOp(And,BinaryOp(Equiv,Letter 3, Letter 5),
            BinaryOp(Equiv,Letter 5,Letter 7))
  in
    BinaryOp(Or,wh1, BinaryOp(Or,wh2, BinaryOp(Or,wh3,
    BinaryOp(Or,wv1, BinaryOp(Or,wv2, BinaryOp(Or,wv3,
                              BinaryOp(Or,wd1,wd2)))))));;
                             
let tictac = 
  let _ = print_endline "All set for playing tic-tac-toe? Go on!!"
  in
    let rec helper t h player p = 
      let _ = Printf.printf "Player %d, please enter cell number 1 - 9 \n" player
      and _ = flush stdout
      and c = int_of_string (input_line stdin)
      in
        if (c>9 || c<1)
        then 
          let _ = print_endline "Please enter a valid cell number (1-9)"
          and _ = flush stdout
          in
            helper t h player p
        else
          let bdd1 = build t h p 9
          and b = match player with 
            | 1 -> True
            | 2 -> False
          in
            let w = substitution p (c,b)
            in
            (* If bdds are same then the cell is already filled *)
              let bdd2 = build t h w 9
              in
                if bdd1=bdd2
                then 
                  let _ = print_endline "This cell is already filled, please enter an empty cell number"
                  and _ = flush stdout
                  in
                    helper t h player p
                else match bdd2 with 
                | 0 -> 
                  let _ = print_endline "Draw......."
                  in
                    flush stdout
                | 1 -> 
                  let _ = Printf.printf "Player %d wins the game.\n" player
                  in
                    flush stdout
                | _ -> helper t h (3-player) w
    in
      helper (initT 9) (initH 9) 1 winningMoves;;
