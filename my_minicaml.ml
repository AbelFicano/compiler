(* This is an OCaml editor.
   Enter your program here and send it to the toplevel using the "Eval code"
   button or [Ctrl-e]. *)

type id = string ;;

type exp =
  |CstInt of int
  |CstTrue
  |CstFalse
  |Add of exp*exp
  |Sub of exp*exp
  |Mul of exp*exp
  |Div of exp*exp
  |Eq of exp*exp
  |And of exp*exp
  |Or of exp*exp
  |Not of exp
  |IfThenElse of exp*exp*exp
  |Den of id
  |Let of id*exp*exp
  |Fun of id*exp
  |Apply of exp*exp
  |LetRec of id*id*exp*exp
  |BiFun of id*id*exp
  |BiApply of exp*exp*exp
  |Empty
  |Cons of exp*exp
  |Length of exp
  |SumAll of exp
  |BothFun of id*exp*exp
  |CodaLimitata of exp
  |Insert of exp*exp
  |Remove of exp
  |Peek of exp
  |CstLista of int list
  |ForEach of exp*exp
  |CFun of exp*exp*exp;;

type types =
  |TInt
  |TBool
  |TList
  |TCoda;;

type 't env = id -> 't ;; 

type evT =
  |Int of int
  |Bool of bool
  |Unbound
  |Closure of id*exp*(evT env)
  |RecClosure of id*id*exp*(evT env)
  |BiClosure of id*id*exp*(evT env)
  |List of int list
  |BothClosure of id*exp*exp*(evT env)
  |Pair of evT*evT
  |Coda of (evT list)*int
  |Lista of int list
  |CClosure of evT*evT*evT;;

let empty_env = fun i -> Unbound ;;

let bind s b v =
  fun i -> if i = b then v else (s i) ;;

let typecheck type' value =
  match type' with
  |TInt -> (match value with
      |Int n -> true
      |_ -> false)
  |TBool -> (match value with
      |Bool b -> true
      |_ -> false)
  |TList -> (match value with
      |List l -> true
      |_ -> false)
  |TCoda -> (match value with
      |Coda (lis, n) -> true
      |_ -> false);;

let add e1 e2 =
  match (typecheck TInt e1, typecheck TInt e2, e1, e2) with
  |(true, true, Int n1, Int n2) -> Int (n1 + n2)
  |_ -> failwith "Invalid add" ;;

let sub e1 e2 =
  match (typecheck TInt e1, typecheck TInt e2, e1, e2) with
  |(true, true, Int n1, Int n2) -> Int (n1 - n2)
  |_ -> failwith "Invalid sub" ;;

let mul e1 e2 =
  match (typecheck TInt e1, typecheck TInt e2, e1, e2) with
  |(true, true, Int n1, Int n2) -> Int (n1 * n2)
  |_ -> failwith "Invalid mul" ;;

let div e1 e2 =
  match (typecheck TInt e1, typecheck TInt e2, e1, e2) with
  |(true, true, Int n1, Int n2) -> Int (n1 / n2)
  |_ -> failwith "Invalid div" ;;

let eq e1 e2 =
  match (typecheck TInt e1, typecheck TInt e2, e1, e2) with
  |(true, true, Int n1, Int n2) -> Bool (n1 = n2)
  |_ -> failwith "Invalid eq" ;;

let and' e1 e2 =
  match (typecheck TBool e1, typecheck TBool e2, e1, e2) with
  |(true, true, Bool true, Bool true) -> Bool true
  |(true, true, _, _) -> Bool false
  |_ -> failwith "Invalid and" ;;

let or' e1 e2 =
  match (typecheck TBool e1, typecheck TBool e2, e1, e2) with
  |(true, true, Bool false, Bool false) -> Bool false
  |(true, true, _, _) -> Bool true
  |_ -> failwith "Invalid or" ;;

let not e' =
  match (typecheck TBool e', e') with
  |(true, Bool true) -> Bool false
  |(true, _) -> Bool true
  |_ -> failwith "Invalid not" ;;

let cons e1 e2 =
  match (typecheck TInt e1, typecheck TList e2, e1, e2) with
  |(true, true, Int n, List l) -> List (n::l)
  |_ -> failwith "Invalid cons" ;;

let length e =
  match (typecheck TList e, e) with
  |(true, List l) -> let rec reclength lis =
                       match lis with
                       |[] -> 0
                       |n::lis' -> 1 + reclength lis'
      in Int (reclength l) 
  |_ -> failwith "Invalid length";;

let sumall e =
  match (typecheck TList e, e) with
  |(true, List l) -> let rec recsumall lis =
                       match lis with
                       |[] -> 0
                       |n::lis' -> n + recsumall lis'
      in Int (recsumall l)
  |_ -> failwith "Invalid sumall" ;;

let rec eval (e: exp) (s: evT env) =
  match e with
  |CstInt n -> Int n
  |CstTrue -> Bool true
  |CstFalse -> Bool false
  |Add (e1, e2) -> add (eval e1 s) (eval e2 s)
  |Sub (e1, e2) -> sub (eval e1 s) (eval e2 s)
  |Mul (e1, e2) -> mul (eval e1 s) (eval e2 s)
  |Div (e1, e2) -> div (eval e1 s) (eval e2 s)
  |Eq (e1, e2) -> eq (eval e1 s) (eval e2 s)
  |And (e1, e2) -> and' (eval e1 s) (eval e2 s)
  |Or (e1, e2) -> or' (eval e1 s) (eval e2 s)
  |Not e' -> not (eval e' s)
  |IfThenElse (e', e1, e2) ->
      (let g = eval e' s in
       match (typecheck TBool g, g) with
       |(true, Bool true) -> eval e1 s
       |(true, Bool false) -> eval e2 s 
       |_ -> failwith "Invalid guard")
  |Den i -> s i
  |Let (i,v,e') ->
      let s' = bind s i (eval v s) in
      eval e' s' 
  |Fun (x, body) -> Closure (x, body, s) 
  |LetRec (f, x, body, e') -> 
      let s' = bind s f (RecClosure (f, x, body, s)) in
      eval e' s'
  |BothFun (x, e1, e2) -> BothClosure (x, e1, e2, s)
  |Apply (fun', arg) ->
      (match eval fun' s with
       |Closure (x, body, fEnv) ->
           let argVal = eval arg s in
           let newEnv = bind fEnv x argVal in
           eval body newEnv
       |RecClosure (f, x, body, fEnv) ->
           let argVal = eval arg s in
           let newEnv = bind (bind fEnv f (RecClosure (f, x, body, fEnv))) x argVal in
           eval body newEnv
       |BothClosure (x, body1, body2, fEnv) ->
           let newEnv = bind fEnv x (eval arg s) in
           let v1 = eval body1 newEnv in
           let v2 = eval body2 newEnv in
           Pair (v1, v2)
       |CClosure (Closure (x1, body1, env1), Closure (x2, body2, env2), Closure (x3, body3, env3)) -> 
           (let argVal = eval arg s in
            let g = eval body1 (bind env1 x1 argVal) in
            match (typecheck TBool g, g) with
            |(true, Bool true) -> eval body2 (bind env2 x2 argVal)
            |(true, Bool false) -> eval body3 (bind env3 x3 argVal)
            |_ -> failwith "Invalid apply of cfun" )
       |_ -> failwith "Invalid function")
  |BiFun (x, y, body) -> BiClosure (x, y, body, s)
  |BiApply (fun', argx, argy) ->
      (match eval fun' s with
       |BiClosure (x, y, body, fEnv) ->
           let xVal = eval argx s in
           let yVal = eval argy s in
           let newEnv = bind (bind fEnv x xVal) y yVal in
           eval body newEnv
       |_ -> failwith "Invalid function")
  |Empty -> List []
  |Cons (e1, e2) -> cons (eval e1 s) (eval e2 s)
  |Length e -> length (eval e s)
  |SumAll e -> sumall (eval e s)
  |CodaLimitata e' -> (let len = eval e' s in
                       match (typecheck TInt len, len) with
                       |(true, Int n) -> Coda ([], n)
                       |_ -> failwith "Invalid coda")
  |Insert (e1, e2) -> (let coda = eval e1 s in
                       let el = eval e2 s in
                       match (typecheck TCoda coda, coda) with
                       |(true, Coda (lis, n)) -> if List.length lis < n then Coda (lis@[el], n)
                           else failwith "Full coda"
                       |_ -> failwith "Invalid insert")
  |Remove e' -> (let coda = eval e' s in
                 match (typecheck TCoda coda, coda) with
                 |(true, Coda (lis, n)) -> (match lis with
                     |[] -> failwith "Empty coda"
                     |el::lis' -> Coda (lis', n) )
                 |_ -> failwith "Invalid remove" )
  |Peek e' -> (let coda = eval e' s in
               match (typecheck TCoda coda, coda) with
               |(true, Coda (lis, n)) -> (match lis with
                   |[] -> failwith "Empty coda"
                   |el::lis' -> el )
               |_ -> failwith "Invalid remove" )
  |CstLista lis -> if lis=[] then failwith "Error"
      else Lista lis
  |ForEach (e1, e2) -> (match (eval e1 s, eval e2 s) with
      |(Lista lis, Closure (x, body, fenv)) -> 
          let rec foreach lis acc =
            match lis with
            |[] -> acc
            |el::lis' -> let newenv = bind fenv x (Int el) in
                let newacc = add (eval body newenv) acc in
                foreach lis' newacc
          in foreach lis (Int 0)
      |_ -> failwith "Invalid for each")
  |CFun (e1, e2, e3) -> CClosure (eval e1 s, eval e2 s, eval e3 s)
;; 