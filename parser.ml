open Program
exception SyntaxError of string
let synerr s = raise (SyntaxError s)

(* small example programs:
   Because we're keeping type inference simple, we'll require functions to have a single argument,
   and declare the type of that argument after a colon.
   To simplify parsing function applications, we'll have explicit "app" expressions, so to apply function f to argument x,
   the program will say (app f x).  A multiple argument function will need to be applied to each argument in turn, so the equivalent to the
   Ocaml expression (f x y) will be (app (app f x) y).
*)
let example1 =
  "(let f (fun g : int -> int  (app g 0))
          (print (app f (fun x : int (+ x 2)))))"

let example2 =
  "(let gcd (fun a : int (fun b : int
            (let q (/ a b)
            (let r (- a (* q b))
                   (seq (while (not (= r 0))
                               (seq (set a b)
                                    (set b r)
                                    (set q (/ a b))
                                    (set r (- a (* q b)))))
                         b)))))
            (print (app (app gcd 217) 527)))"

let example3 =
"(let y 0
    (let x (+ 1 2)
        (while (> x 0)
            (seq
                (set x (- x 1))
                (if (> 1 0) x y)
                (if (< 1 0) x y)
                (while (> 1 0) (print y))
                (+ 1 2)
                (seq (let z (+ 2 3) (< 1 2)))
            )
        )
    )
)"

let example4 =
"(let y (* 0 0)
  (let z (if (> y 4)
           (seq (set y (- y 1)) 1)
           0)
    (seq (print y)
         (if (= (+ 1 0) (- 2 1))
             (let z readint z)
             (+ 42 17)))
  )
)"

(* We want this one to work, eventually *)
let example5 =
"(let rev
    (fun in : list
      (let out []
        (seq
          (while (not (= in []))
            (seq
              (set out (cons (head in) out))
              (set in (tail in))))
          out)))
    (app rev [1 2 3 4 5]))"

(* And this longer one, too... *)
let example6 =
"(let readlist
    (fun x : unit
      (let out []
      (let cont true
      (let x 0
      (seq
      (while cont
        (seq
          (set x readint)
          (if (< x 0) (set cont false) (set out (cons x out)))))
      out)))))
(let printlist
  (fun l : list
    (while (not (= l []))
      (seq
        (print (head l))
        (set l (tail l)))))
(let rev
  (fun in : list
    (let out []
      (seq
        (while (not (= in []))
          (seq
            (set out (cons (head in) out))
            (set in (tail in))))
        out)))
(app printlist (app rev (app readlist ()))))))"

(* all of the lexical tokens we might encounter in a program *)
type token = CONS | TAIL | HEAD | LIST | READ | LETREC | LB | RB |  OP | CP | AND | OR | NOT | PLUS | MINUS | TIMES | DIV | LET | ID of string | ICONST of int | BCONST of bool | LT | GT | EQ | IF |
	     SET | SEQ | WHILE | PRINT |
	     APP | FUN | COLON | ARROW | INT | BOOL | UNIT


(* Split a string into a list of words, delimited by spaces, parens, colons, and -> *)
(* never mind the magic regexp *)
let wordlist s =
  let splitlist = Str.full_split (Str.regexp "\\b\\|(\\|)\\|:\\|\\(->\\)\\|\\[\\|\\]") s in
  let rec filter_splist lst = match lst with
    | [] -> []
    | (Str.Delim "(")::t -> "(" :: (filter_splist t)
    | (Str.Delim ")")::t -> ")" :: (filter_splist t)
    | (Str.Delim "[")::t -> "[" :: (filter_splist t)
    | (Str.Delim "]")::t -> "]" :: (filter_splist t)
    | (Str.Delim "->")::t -> "->" :: (filter_splist t)
    | (Str.Delim ":")::t -> ":"::(filter_splist t)
    | (Str.Delim _) :: t -> filter_splist t
    | (Str.Text s) :: t -> let s' = String.trim s in
                           let t' = (filter_splist t) in
                           if not (s' = "") then s' :: t' else t'
  in filter_splist splitlist

(* turn a word into a token *)
let tokenize_string = function
  | "(" -> OP
  | ")" -> CP
  | "[" -> LB
  | "]" -> RB
  | "letrec" -> LETREC
  | "list" -> LIST
  | "cons" -> CONS
  | "head" -> HEAD
  | "tail" -> TAIL
  | "readint" -> READ
  | "and" -> AND
  | "or" -> OR
  | "not" -> NOT
  | "+" -> PLUS
  | "*" -> TIMES
  | "-" -> MINUS
  | "/" -> DIV
  | "let" -> LET
  | ">" -> GT
  | "<" -> LT
  | "=" -> EQ
  | "if" -> IF
  | "set" -> SET
  | "seq" -> SEQ
  | "while" -> WHILE
  | "app" -> APP
  | "fun" -> FUN
  | ":" -> COLON
  | "->" -> ARROW
  | "int" -> INT
  | "bool" -> BOOL
  | "unit" -> UNIT
  | "print" -> PRINT
  | "true" -> BCONST true
  | "false" -> BCONST false
  | s -> if Str.string_match (Str.regexp "[0-9]+") s 0 then (ICONST (int_of_string s))
	 else if Str.string_match (Str.regexp "[a-z]+") s 0 then (ID s) else synerr ("invalid token:"^s)

(* and a list of words into a list of tokens *)
let tokens wl = List.map tokenize_string wl

(* Parse a type expression in a function definition.
   Return the type and the list of unused tokens for further parsing.
   A type expression is either: INT, BOOL, UNIT, LIST or  (typeExpr)  or typeExpr -> typeExpr  *)
let rec _parse_type_expr tlist =
  let (ty1, tl) =
    match tlist with
    | INT::t -> (IntT,t)
    | BOOL::t -> (BoolT,t)
    | UNIT::t -> (UnitT,t)
    | LIST::t -> (ListT,t)
    (* Read up until we find a close paren: covers types like "(int->bool) -> int" *)
    | OP::t -> (match _parse_type_expr t with
                | ty, CP::t' -> (ty,t')
	              | _,t' -> synerr "imbalanced parentheses in type expression")
    | _ -> synerr "unexpected token in type expression."
  in match tl with (* peek at tail: is there an arrow (so more type expr to read)? *)
     | ARROW::t1 -> let (ty2, t2) = _parse_type_expr t1 in (FunT(ty1,ty2),t2)
     | _ -> (ty1,tl) (* No, we're done here. *)

(* parse an expression from a list of tokens, returning the expression and the list of unused tokens *)
let rec _parser tlist = match tlist with
| [] -> synerr "Ran out of tokens without closing parenthesis" []
| (BCONST b)::t -> (BoolC b,t)
| (ICONST i)::t -> (IntC i, t)
| (ID s)::t -> (Name s, t)
| OP::LETREC::t -> let (s,f,e2,t') = _parse_letrec t in (Let (s,f,e2),t')
| LB::t -> let (l,t') = _parse_literal t in (ListC (l),t')
| READ::t -> (Readint, t)
| OP::CONS::t -> let (e1,e2,t') = _parse_two t in (Cons (e1,e2), t')
| OP::PLUS::t -> let (e1,e2,t') = _parse_two t in (Add (e1,e2), t')
| OP::MINUS::t -> let (e1,e2,t') = _parse_two t in (Sub (e1,e2), t')
| OP::TIMES::t -> let (e1,e2,t') = _parse_two t in (Mul (e1,e2), t')
| OP::DIV::t -> let (e1,e2,t') = _parse_two t in (Div (e1,e2), t')
| OP::AND::t -> let (e1,e2,t') = _parse_two t in (And (e1,e2), t')
| OP::OR::t -> let (e1,e2,t') = _parse_two t in (Or (e1,e2), t')
| OP::EQ::t -> let (e1,e2,t') = _parse_two t in (Eq (e1,e2), t')
| OP::GT::t -> let (e1,e2,t') = _parse_two t in (Gt (e1,e2), t')
| OP::LT::t -> let (e1,e2,t') = _parse_two t in (Lt (e1,e2), t')
| OP::WHILE::t -> let (e1,e2,t') = _parse_two t in (While (e1,e2), t')
| OP::APP::t -> let (e1,e2,t') = _parse_two t in (Apply (e1,e2), t')
| OP::FUN::(ID s)::COLON::t ->
       let (tExp, t') = _parse_type_expr t in
       let (bExp,t'') = _parse_single t' in (Fun (s,tExp,bExp),t'')
| OP::LET::(ID s)::t -> let (v,e,t') = _parse_two t in (Let (s,v,e), t')
| OP::SET::(ID s)::t -> let (e,t') = _parse_single t in (Set (s,e), t')
| OP::IF::t -> let (c,t1) = _parser t in
    let (thn,els,t2) = _parse_two t1 in (If (c,thn,els), t2)
| OP::NOT::t -> let (e,t') = _parse_single t in (Not(e),t')
| OP::PRINT::t -> let (e,t') = _parse_single t in (Print(e), t')
| OP::HEAD::t -> let (e,t') = _parse_single t in (Head(e), t')
| OP::TAIL::t -> let (e,t') = _parse_single t in (Tail(e), t')
| OP::SEQ::t -> let (l,t') = _parse_list t in (Seq(l),t')
| OP::CP::t -> (Seq [], t)
| _ -> synerr "Unexpected token: unbalanced parentheses or keyword out of call position"

(* parse a single expression and "eat" the following close paren *)
and _parse_single t = match _parser t with
| e, CP::t'' -> (e,t'')
| _,t' -> synerr "parser: missing closing paren."


(* "eat" the close paren after two expressions *)
and _parse_two t =
  let (e1,t1) = _parser t in
  let (e2,t2) = _parser t1 in
  match t2 with CP::t' -> (e1,e2,t')
  | _ -> synerr "parser: missing closing paren."

(* parse a list of expressions, consuming the final closing paren *)
and _parse_list t =  match t with
| CP::t' -> ([],t')
| [] -> synerr "unfinished expression sequence: missing close paren(s)."
| _ -> let (e,t1) = _parser t in
        let (el,t2) = _parse_list t1 in (e::el, t2)

(* parse a list literal, consuming right bracket*)
and _parse_literal t = (match t with
| RB::t' -> ([],t')
| [] -> raise (SyntaxError "unclosed list")
| (ICONST x )::t' ->
   let (l,t2) = _parse_literal t' in (x::l, t2)
| _-> raise (SyntaxError "list literal"))

(* parse a let rec, consuming the closing paren*)
and _parse_letrec t = (match t with
|(ID s)::COLON::t' -> 
  let (ftype,t1) = _parse_type_expr t' in (*get type*)
  let (e1,e2,t2) = _parse_two t1 in (*get e1,e2*)
  (match (t2) with
    |CP::t3 -> (match e1 with (*if match, do stuff with e1*)
      | Fun(argname,argtype,body) -> (*find function arguments*)
        let f = Funrec(s,argname,ftype,argtype,body) in
        (s,f,e2,t3) (*return function name, f in place of e1, e2, and environment left*)
      | _ -> raise (SyntaxError "letrec must have function value"))
    | _ -> raise (SyntaxError " alr letrec must have function value" ))
| _ -> raise (SyntaxError "letrec"))

let parse_program tlist = match _parser tlist with
| e,[] -> e
| _,t -> synerr "parse failed: extra tokens in input."
