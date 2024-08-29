(* program.ml - a data structure for representing programs *)
exception TypeError of string
exception RuntimeError of string
let rt_err s = raise (RuntimeError s)
let type_err s = raise (TypeError s)

type expr =
  IntC of int | ListC of int list | BoolC of bool 
  | Head of expr
  | Tail of expr
  | Cons of expr * expr
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Div of expr * expr
  | If of expr * expr * expr
  | Let of string * expr * expr
  | Name of string
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | Lt of expr * expr
  | Eq of expr * expr
  | Gt of expr * expr
  | Seq of expr list
  | While of expr * expr
  | Set of string * expr
  | Fun of string * expType * expr
  | Funrec of string * string * expType * expType * expr
  | Apply of expr * expr
  | Print of expr
  | Readint
 and expType = IntT | BoolT | UnitT | FunT of expType * expType | ListT

(* Type to represent a state of the program, e.g. the current stack of variables and the values they are bound to *)
type stType = (string * result) list
 (* Type to represent a value in the program *)
 and result = IntR of int | BoolR of bool | UnitR | ClosureRec of expr*string*string*stType | ListR of (int list) | Closure of expr*string*stType 

(* Searches the stack and updates the most recent binding with the new value *)
let rec assign name value state =
  match state with
  | [] -> rt_err "assign to unbound name"
  | (n,v)::t when n=name -> (name,value)::t
  | b::t -> b::(assign name value t)

(* pop a variable binding off the stack *)
let rec pop name state =
  match state with
  | [] -> rt_err "popping unbound name: internal error"
  | (n,v)::t when n=name -> t
  | b::t -> b::(pop name t)

let rec print_help lst acc = match lst with 
  |h::t -> (acc ^ (string_of_int h) ^ " ")
  |[] -> (acc ^ "]")


(* evaluate an expression: return the value and the new program state *)
let rec eval exp state = match exp with
  | ListC l -> (ListR l, state)
  | IntC n -> (IntR n, state)
  | BoolC b -> (BoolR b, state)
  | Readint -> (IntR (read_int ()), state)
  | Funrec (f,x,t2,t1,e) -> (ClosureRec (e,f,x,state), state)
  | Head l -> let (ListR l2, st) = (eval l state) in (IntR (List.hd l2), st)
  | Tail l -> let (ListR l1, st) = (eval l state) in (ListR (List.tl l1), st)
  | Cons (e1,e2) ->
    let (IntR l1, st1) = (eval e1 state) in
    let (ListR l2, st2) = (eval e2 st1) in
    (ListR (l1::l2), st2)  
  | Add (e1,e2) -> evalInt (+) e1 e2 state
  | Mul (e1,e2) -> evalInt ( * ) e1 e2 state
  | Sub (e1,e2) -> evalInt (-) e1 e2 state
  | Div (e1,e2) -> evalInt (/) e1 e2 state
  | If (cond,thn,els) -> evalIf cond thn els state
  | Let (nm,vl,exp') -> evalLet nm vl exp' state
  | Name nm -> (List.assoc nm state, state)
  | And (e1,e2) -> evalBool (&&) e1 e2 state
  | Or (e1,e2) -> evalBool (||) e1 e2 state
  | Not e -> let (BoolR b, st') = eval e state in (BoolR (not b), st')
  | Lt (e1, e2) -> evalComp (<) e1 e2 state
  | Eq (e1, e2) -> evalComp (=) e1 e2 state
  | Gt (e1, e2) -> evalComp (>) e1 e2 state
  | Seq elist -> evalSeq elist state
  | While (cond,body) -> evalWhile cond body state
  | Set (name, e) -> let (vl, st') = eval e state in (UnitR, assign name vl st')
  | Fun (argname,_,body) -> 
    (Closure (body,argname,state), state) (* "Captures" current environment at definition. *)
  | Apply (f,e) -> evalFunc f e state
  | Print e -> let (r,st') = eval e state in
	       let () = match r with
		 | UnitR -> print_string "()"
     | ListR l -> 
      (let s = (print_help l "[")
      in print_string s)
		 | IntR i -> print_int i     
		 | BoolR b -> print_string (if b then "True" else "False")
     | ClosureRec _ -> (print_string "<funrec>") in
        let () = print_string "\n" in
        let () = flush stdout in
        (UnitR, st')
(*		 | Closure _ -> (print_string "<fun>") in
        let () = print_string "\n" in
        let () = flush stdout in
        (UnitR, st')*)
and evalInt f e1 e2 state =
  let (IntR i1, st1) = eval e1 state in
  let (IntR i2, st2) = eval e2 st1 in
  IntR (f i1 i2), st2
and evalIf cond thn els state =
  let (BoolR b, st') = eval cond state in
  if b then eval thn st' else eval els st'
and evalLet name vl exp state =
  let (r, st') = eval vl state in
  let (r', st'') = eval exp ((name,r)::st') in
  (r', pop name st'')
and evalBool f e1 e2 state =
  let (BoolR b1, st1) = eval e1 state in
  let (BoolR b2, st2) = eval e2 st1 in
  BoolR (f b1 b2), st2
and evalComp cmp e1 e2 state =
  let (r1, st1) = eval e1 state in
  let (r2, st2) = eval e2 st1 in
  (BoolR (cmp r1 r2), st2)
and evalSeq elist st = match elist with (* Whee, tail recursion. *)
  | [] -> (UnitR, st)
  | e::[] -> eval e st
  | e::t -> let (_, st') = eval e st in
	    evalSeq t st'
and evalWhile cond body st = (* Note the tail recursion. An infinite while loop won't blow the stack *)
  let (BoolR b, st') = eval cond st in
  if (not b) then (UnitR, st') else
    let (_, st'') = eval body st' in
    evalWhile cond body st''
and evalFunc f arg state = match (eval f state) with (* Note: we need to evaluate the function with environment at time of definition *)
  | (Closure (body,argname,def_st), st') ->
    let (argval, st'') = eval arg st' in (* but computing its argument could change state at call site *)
    let (result, _) = eval body ((argname,argval)::def_st) in
    (result, st'') (* So state after call must be the state after argument computation *)
  | (ClosureRec (body,fname,argname,def_st), st') ->
    let (argval, st'') = eval arg st' in 
    let (closure, _) = (ClosureRec (body,fname,argname,def_st), st') in
    let (result, _) = eval body ((fname,closure)::(argname,argval)::def_st) in
    (result, st'')

(* Type checking/inference: Figure out type for an expression.  Fail if the expression is not well-typed.*)
let rec typeof exp env = match exp with
  | ListC _ -> ListT
  | IntC _ -> IntT
  | BoolC _ -> BoolT
  | Readint -> IntT
  | Head e -> (match (typeof e env) with 
    | ListT -> IntT
    | _ -> raise (TypeError "Head"))
  | Tail e -> (match (typeof e env) with 
    | ListT -> ListT
    | _ -> raise (TypeError "Tail"))
  | Cons (e1,e2) -> (match (typeof e1 env, typeof e2 env) with
    | (IntT, ListT) -> ListT
    | (_,_) -> raise (TypeError "Cons"))
  | Add (e1,e2) | Sub (e1,e2) | Mul (e1,e2)
  | Div (e1,e2) ->
     ( match (typeof e1 env, typeof e2 env) with
       | (IntT,IntT) -> IntT
       | _ -> type_err "Arithmetic on non-integer arguments")
  | And (e1,e2)
  | Or (e1,e2) ->
     ( match (typeof e1 env, typeof e2 env) with
       | (BoolT,BoolT) -> BoolT
       | _ -> type_err "Boolean operation on non-Bool arguments")
  | Not e -> if (typeof e env) = BoolT then BoolT else type_err "Not of non-Boolean"
  | Lt (e1,e2)
  | Gt (e1,e2) ->
     ( match (typeof e1 env, typeof e2 env) with
       | (IntT,IntT) -> BoolT
       | _ -> type_err "Comparison of non-integer values" )
  | Eq (e1,e2) ->
     ( match (typeof e1 env, typeof e2 env) with
       | (IntT,IntT) | (BoolT,BoolT) | (UnitT,UnitT) | (ListT,ListT) -> BoolT
       | _ -> type_err "Equality test on incompatible values" )
  | If (cond,thn,els) ->
     if not ((typeof cond env) = BoolT) then type_err "If on non-boolean condition" else
       let (t1,t2) = (typeof thn env, typeof els env) in
       if (t1 = t2) then t1 else type_err "Different types for then/else branches"
  | Name name -> (try List.assoc name env with Not_found -> type_err ("Unbound variable "^name))
  | Let (name,vl,e) ->
     let t = typeof vl env in
     typeof e ((name,t)::env)
  | Seq elist -> seqType elist env
  | While (c,body) ->
     ( match (typeof c env, typeof body env) with
       | (BoolT, _) -> UnitT
       | _ -> type_err "Non-boolean condition for while")
  | Set (name, e) -> if (typeof (Name name) env) = (typeof e env) then UnitT else type_err "assign type mismatch"
  | Fun (argname, argType, body) ->
     let resType = typeof body ((argname,argType)::env) in
     FunT (argType,resType)
  | Funrec (f,x,t2,t1,e) -> 
   (if (typeof e ((f, FunT(t1,t2))::(x,t1)::env) = t2) 
   then (FunT (t1,t2)) 
   else raise (TypeError ""))
  | Apply (e1,e2) ->
     ( match (typeof e1 env) with
       | FunT (argtype, restype) -> if (typeof e2 env) = argtype then restype
				       else type_err "incompatible function argument"
       | _ -> type_err "Apply of non-function value")
  | Print e -> let _ = typeof e env in UnitT
and seqType el env = match el with
  | [] -> UnitT
  | [e] -> typeof e env
  | e::rest -> let _ = typeof e env in seqType rest env
  

