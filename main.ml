(* Definitions *)
type variable = string

type newVariable = NewVariable of string * newVarGenerator and newVarGenerator = unit -> newVariable

type typeDef = TypeInt 
			| TypeBool 
			| TypeId of string 
			| TypeFn of typeDef * typeDef 
			| TypeList of typeDef
			| TypePair of typeDef * typeDef 

type binaryOperator = Sum 
					| Sub 
					| Mult 
					| Div 
					| Equal 
					| Diff 
					| Less 
					| LessOrEqual 
					| Greater 
					| GreaterOrEqual 
					| And 
					| Or

type unaryOperator = Not

type value = ValueNum of int
			| ValueBool of bool
			| ValueNil 
			| ValueCons of value * value
			| ValueRaise
			| VPair of value * value

type env = (variable * value) list

type typeEnv = (variable * typeDef) list

type typeEquations = (typeDef * typeDef) list

type expression = Nval of int
				| Bval of bool
				| Binop of binaryOperator * expression * expression
				| Unop of unaryOperator * expression
				| Pair of expression * expression
				| Fst of expression
				| Snd of expression
				| If of expression * expression * expression
				| Id of variable
				| App of expression * expression
				| Fn of variable * expression
				| Let of variable * expression * expression
				| Letrec of variable * variable * expression * expression
				| Nil
				| Cons of expression * expression
				| Hd of expression
				| Tl of expression
				| Isempty of expression
				| Raise
				| Try of expression * expression

(* Exceptions *)
exception VariableError of string
exception OperationError of string
exception UnifyError of string

(* Utils *)
let rec generator n () = NewVariable("#x" ^ string_of_int n, generator (n + 1))
let varGenerator = generator 0

let rec lookup environment x = match environment with
	| (y, v)::tail -> if (String.compare y x) == 0 then v else (lookup tail x)
	| [] -> raise (VariableError("Variable not found in environment"))

(* Inferator *)
let rec collect_rec (environment: typeEnv) (program: expression) (varGen: newVarGenerator) = match program with
	| Nval(v) -> (TypeInt, [], varGen)

	| Bval(v) -> (TypeBool, [], varGen)

	| Binop(op, e1, e2) -> (
		(match op with
			| Sum | Sub | Mult | Div ->
				let (type1, eq1, gen1) = collect_rec environment e1 varGen in
				let (type2, eq2, gen2) = collect_rec environment e2 gen1 in
				let new_eq = [(type1, TypeInt); (type2, TypeInt)] in
				(TypeInt, List.concat [eq1; eq2; new_eq], gen2)
			| Equal | Diff | Less | LessOrEqual | Greater | GreaterOrEqual ->
				let (type1, eq1, gen1) = collect_rec environment e1 varGen in
				let (type2, eq2, gen2) = collect_rec environment e2 gen1 in
				let new_eq = [(type1, TypeInt); (type2, TypeInt)] in
				(TypeBool, List.concat [eq1; eq2; new_eq], gen2)
			| And | Or ->
				let (type1, eq1, gen1) = collect_rec environment e1 varGen in
				let (type2, eq2, gen2) = collect_rec environment e2 gen1 in
				let new_eq = [(type1, TypeBool); (type2, TypeBool)] in
				(TypeBool, List.concat [eq1; eq2; new_eq], gen2)
		)	
	)

	| Unop(op, e) -> (
		(match op with
			| Not -> 
				let (type1, eq1, gen1) = collect_rec environment e varGen in
				let new_eq = [(type1, TypeBool)] in
				(TypeBool, List.concat [eq1; new_eq], gen1)
		)
	)

	| Pair(e1, e2) ->
		let (type1, eq1, gen1) = collect_rec environment e1 varGen in
		let (type2, eq2, gen2) = collect_rec environment e2 gen1 in
		(TypePair(type1, type2), List.concat [eq1; eq2], gen2)

	| Fst(e) -> 
		let NewVariable(newVar1, newGen1) = varGen () in 
		let NewVariable(newVar2, newGen2) = newGen1 () in 
		let (type1, eq1, gen3) = collect_rec environment e newGen2 in
		let x = TypeId(newVar1) in
		let y = TypeId(newVar2) in
		let new_eq = [(type1, TypePair(x, y))] in
		(x, List.concat [eq1; new_eq], gen3)

	| Snd(e) -> 
		let NewVariable(newVar1, newGen1) = varGen () in 
		let NewVariable(newVar2, newGen2) = newGen1 () in 
		let (type1, eq1, gen3) = collect_rec environment e newGen2 in
		let x = TypeId(newVar1) in
		let y = TypeId(newVar2) in
		let new_eq = [(type1, TypePair(x, y))] in
		(y, List.concat [eq1; new_eq], gen3)

	| If(e1, e2, e3) ->
		let (type1, eq1, gen1) = collect_rec environment e1 varGen in
		let (type2, eq2, gen2) = collect_rec environment e2 gen1 in
		let (type3, eq3, gen3) = collect_rec environment e3 gen2 in
		let new_eq = [(type1, TypeBool); (type2, type3)] in
		(type2, List.concat [eq1; eq2; eq3; new_eq], gen3)

	| Id(x) -> 
		(try 
			(let typeT = lookup environment x in
			(typeT, [], varGen))
		with
			_ -> raise (VariableError "Variable not found in environment"))

	| App(e1, e2) ->
		let (type1, eq1, gen1) = collect_rec environment e1 varGen in
		let (type2, eq2, gen2) = collect_rec environment e2 gen1 in
		let NewVariable(newVar, newGen) = gen2 () in 
		let x = TypeId(newVar) in
		let new_eq = [(type1, TypeFn(type2, x))] in
		(x, List.concat [eq1; eq2; new_eq], newGen)

	| Fn(y, e) ->
		let NewVariable(newVar, newGen) = varGen () in 
		let x = TypeId(newVar) in
		let (type1, eq1, gen1) = collect_rec (List.concat [environment; [(y, x)]]) e newGen in
		(TypeFn(x, type1), eq1, gen1)

	| Let(y, e1, e2) ->
		let NewVariable(newVar, newGen) = varGen () in 
		let x = TypeId(newVar) in
		let (type1, eq1, gen1) = collect_rec environment e1 newGen in
		let (type2, eq2, gen2) = collect_rec (List.concat [environment; [(y, x)]]) e2 gen1 in
		let new_eq = [(x, type1)] in
		(type2, List.concat [eq1; eq2; new_eq], gen2)

	| Letrec(a, b, e1, e2) ->
		let NewVariable(newVar1, newGen1) = varGen () in 
		let NewVariable(newVar2, newGen2) = newGen1 () in
		let x = TypeId(newVar1) in 
		let y = TypeId(newVar2) in
		let (type1, eq1, gen1) = collect_rec (List.concat [environment; [(a, x)]; [(b, y)]]) e1 newGen2 in
		let (type2, eq2, gen2) = collect_rec (List.concat [environment; [(a, x)]]) e2 gen1 in
		let new_eq = [(x, TypeFn(y, type1))] in
		(type2, List.concat [eq1; eq2; new_eq], gen2)

	| Nil -> 
		let NewVariable(newVar, newGen) = varGen () in 
		let x = TypeId(newVar) in 
		(TypeList(x), [], newGen)

	| Cons(e1, e2) ->
		let (type1, eq1, gen1) = collect_rec environment e1 varGen in
		let (type2, eq2, gen2) = collect_rec environment e2 gen1 in
		let new_eq = [(TypeList(type1), type2)] in
		(type2, List.concat [eq1; eq2; new_eq], gen2)

	| Hd(e) -> 
		let (type1, eq1, gen1) = collect_rec environment e varGen in
		let NewVariable(newVar, newGen) = gen1 () in
		let x = TypeId(newVar) in
		let new_eq = [(type1, TypeList(x))] in
		(x, List.concat [eq1; new_eq], newGen)

	| Tl(e) ->
		let (type1, eq1, gen1) = collect_rec environment e varGen in
		let NewVariable(newVar, newGen) = gen1 () in
		let x = TypeId(newVar) in
		let new_eq = [(type1, TypeList(x))] in
		(TypeList(x), List.concat [eq1; new_eq], newGen)

	| Isempty(e) ->
		let (type1, eq1, gen1) = collect_rec environment e varGen in
		let NewVariable(newVar, newGen) = gen1 () in
		let x = TypeId(newVar) in
		let new_eq = [(type1, TypeList(x))] in
		(TypeBool, List.concat [eq1; new_eq], newGen)

	| Raise -> 
		let NewVariable(newVar, newGen) = varGen () in 
		let x = TypeId(newVar) in 
		(x, [], newGen)

	| Try(e1, e2) -> 
		let (type1, eq1, gen1) = collect_rec environment e1 varGen in
		let (type2, eq2, gen2) = collect_rec environment e2 gen1 in
		let new_eq = [(type2, type2)] in
		(type2, List.concat [eq1; eq2; new_eq], gen2)

let collect (environment: typeEnv) (program: expression) = collect_rec environment program varGenerator

let rec occur_check (x: string) (t: typeDef) : bool = match t with
	| TypeInt -> false
	| TypeBool -> false
	| TypeId(y) -> (y = x)
	| TypeList(t1) -> (occur_check x t1)
	| TypeFn(t1, t2) -> (occur_check x t1) || (occur_check x t2)
	| TypePair(t1, t2) -> (occur_check x t1) || (occur_check x t2)

let rec typesub (x: string) (t1: typeDef) (t2: typeDef) : typeDef = match t2 with
	| TypeInt -> TypeInt

	| TypeBool -> TypeBool

	| TypeId(y) -> if occur_check x (TypeId(y)) then t1 else TypeId(y)
	
	| TypeList(t) -> let new_type = typesub x t1 t in TypeList(new_type)
	
	| TypeFn(t3, t4) -> 
		let new_type3 = typesub x t1 t3 in
		let new_type4 = typesub x t1 t4 in
		TypeFn(new_type3, new_type4)

	| TypePair(t3, t4) -> 
		let new_type3 = typesub x t1 t3 in
		let new_type4 = typesub x t1 t4 in
		TypePair(new_type3, new_type4)

let rec typesub_equation (x: string) (t: typeDef) (type_equations: typeEquations) : typeEquations = match type_equations with
	| (t1, t2) :: c -> List.append [(typesub x t t1, typesub x t t2)] (typesub_equation x t c)
	| [] -> []

let rec unify (type_equations: typeEquations) : typeEquations = match type_equations with
	| [] -> []

	| (TypeInt, TypeInt) :: c -> unify c

	| (TypeBool, TypeBool) :: c -> unify c

	| (TypeList(t1), TypeList(t2)) :: c ->  unify ((t1, t2) :: c)

	| (TypeFn(t1, t2), TypeFn(t3, t4)) :: c -> unify ((t1, t3) :: (t2, t4) :: c)

	| (TypePair(t1, t2), TypePair(t3, t4)) :: c -> unify ((t1, t3) :: (t2, t4) :: c)

	| (TypeId(_), TypeId(_)) :: c -> unify c

	| (TypeId(x), t) :: c ->
		if occur_check x t then
			raise (UnifyError "x occurs in t.")
		else
			let substitutions = typesub_equation x t c in
			let new_unification = unify substitutions in
			List.append new_unification [(TypeId(x), t)]

	| (t, TypeId(x)) :: c -> 
		if occur_check x t then
			raise (UnifyError "x occurs in t.")
		else
			let substitutions = typesub_equation x t c in
			let new_unification = unify substitutions in
			List.append new_unification [(TypeId(x), t)]

	| (_, _) :: c -> raise (UnifyError "Cannot solve type equations.")

let rec applysubs (type_equations: typeEquations) (t: typeDef) : typeDef = match type_equations with
	| (TypeId(x), t1) :: c -> typesub x t1 (applysubs c t)
	| [] -> t
	| _ -> raise (VariableError("Pattern not found"))

let typeinfer (environment: typeEnv) (program: expression) : typeDef = 
	let (prog_type, type_equations, varGen) = collect environment program in
	let unification = unify type_equations in
	applysubs unification prog_type

(* Bigstep *)
(* let rec eval_rec (env: environment) (e: expression) : value = match e with
	| Nval(n) -> ValueNum(n)

	| Bval(n) -> ValueBool(n)

	| Binop(op, e1, e2) ->

	| Unop(op, e1) ->

	| Pair(e1, e2) ->

	| Fst(e1) ->
	
	| Snd(e1) ->
	
	| If(e1, e2,  e3) ->

	| Id(x) ->

	| App(e1, e2) ->
	
	| Fn(x, e1) ->
	
	| Let(x, e1, e2) ->

	| Letrec(x, y, e1, e2) ->

	| Nil -> ValueNil
	
	| Cons(e1, e2) ->
	
	| Hd(e1) ->

	| Tl(e1) ->
	
	| Isempty(e1) ->
	
	| Raise -> ValueRaise
	
	| Try(e1, e2) ->

let eval (e: expression) : value = eval_rec [] e *)

(* Tests *)
(* Test cases *)
let e0 = Nval(5)

let e1 = Nval(10)

let e2 = Bval(true)

let e3 = Bval(false)

let e4 = Binop(Sum, e0, e1)

let e5 = Binop(Sub, e1, e0)

let e6 = Binop(Mult, e1, e0)

let e7 = Binop(Div, e1, e0)

let e8 = Binop(Equal, e1, e0)
let e9 = Binop(Equal, e1, e1)

let e10 = Binop(Diff, e1, e0)
let e11 = Binop(Diff, e1, e1)

let e12 = Binop(Less, e1, e1)
let e13 = Binop(Less, e1, e0)
let e14 = Binop(Less, e0, e1)

let e15 = Binop(LessOrEqual, e1, e1)
let e16 = Binop(LessOrEqual, e1, e0)
let e17 = Binop(LessOrEqual, e0, e1)

let e18 = Binop(Greater, e1, e1)
let e19 = Binop(Greater, e1, e0)
let e20 = Binop(Greater, e0, e1)

let e21 = Binop(GreaterOrEqual, e1, e1)
let e22 = Binop(GreaterOrEqual, e1, e0)
let e23 = Binop(GreaterOrEqual, e0, e1)

let e24 = Binop(And, e2, e2)
let e25 = Binop(And, e3, e2)

let e26 = Binop(Or, e2, e2)
let e27 = Binop(Or, e3, e2)

let e28 = Unop(Not, e2)
let e29 = Unop(Not, e3)

let e30 = Pair(e0, e1)
let e31 = Fst(e30)
let e32 = Snd(e30)

let e33 = If(e2, e0, e1)
let e34 = If(e3, e0, e1)
let e35 = If(e3, e3, e2)

let e36 = Fn("var_teste1", Binop(Sum, Id("var_teste1"), e0))
let e37 = App(e36, e1)

let e38 = Let("var_teste3", e0, Binop(Mult, Id("var_teste3"), e0))

let e39 = Letrec("factorial", "x", 
                 If(Binop(Equal, Id("x"), Nval(0)), 
                    Nval(1), 
                    Binop(Mult, Id("x"), App(Id("factorial"), Binop(Sub, Id("x"), Nval(1))))), 
                 App(Id("factorial"), e0))

let e40 = Letrec("fibonacci", "x", 
                 If(Binop(LessOrEqual, Id("x"), Nval(0)), 
                    Nval(0), 
                    Binop(Sum, 
                    	  App(Id("fibonacci"), Binop(Sub, Id("x"), Nval(1))),
                    	  App(Id("fibonacci"), Binop(Sub, Id("x"), Nval(2))))), 
                 App(Id("fibonacci"), e1))

let e41 = Cons(Nval(1), Cons(Nval(2), Cons(Nval(3), Nil)))
let e42 = Cons(e5, Cons(Nval(2), Cons(e4, Nil)))

let e43 = Hd(e41)
let e44 = Tl(e41)

let e45 = Isempty(e42)
let e46 = Isempty(Nil)
let e47 = Isempty(Cons(Nil, Nil))
let e48 = Isempty(Cons(e0, Nil))

let e49 = Try(e24, e6)
let e50 = Try(e24, e25)
let e51 = Try(Raise, e25)

(* Utils *)
let rec type_to_string (t: typeDef) : string = match t with
    | TypeInt -> "Integer"
	| TypeBool -> "Boolean"
    | TypeId(x) -> "id(" ^ x ^ ")"
	| TypeFn(t1, t2) -> "(" ^ (type_to_string t1) ^ ") -> (" ^ (type_to_string t2) ^ ")"
	| TypeList(t1) -> "List of " ^ (type_to_string t1)
    | TypePair(t1, t2) -> "(" ^ (type_to_string t1) ^ ", " ^ (type_to_string t1) ^ ")"

let rec value_to_string (v: value) : string = match v with
    | ValueNum(n) -> string_of_int(n)
	| ValueBool(b) -> string_of_bool(b)
	| ValueNil -> "Nil"
	| ValueCons(v1, v2) -> "cons(" ^ (value_to_string v1) ^ ", " ^ (value_to_string v2) ^ ")"
	| ValueRaise -> "Raise"
	| VPair(v1, v2) -> "(" ^ (value_to_string v1) ^ ", " ^ (value_to_string v2) ^ ")"

let rec expression_to_string (e: expression) : string = match e with
	| Nval(n) -> string_of_int(n)
	| Bval(b) -> string_of_bool(b)
	| Binop(Sum, e1, e2) -> "(" ^ (expression_to_string e1) ^ ") + (" ^ (expression_to_string e2) ^ ")"
	| Binop(Sub, e1, e2) -> "(" ^ (expression_to_string e1) ^ ") - (" ^ (expression_to_string e2) ^ ")"
	| Binop(Mult, e1, e2) -> "(" ^ (expression_to_string e1) ^ ") * (" ^ (expression_to_string e2) ^ ")"
	| Binop(Div, e1, e2) -> "(" ^ (expression_to_string e1) ^ ") / (" ^ (expression_to_string e2) ^ ")"
	| Binop(Equal, e1, e2) -> "(" ^ (expression_to_string e1) ^ ") == (" ^ (expression_to_string e2) ^ ")"
	| Binop(Diff, e1, e2) -> "(" ^ (expression_to_string e1) ^ ") != (" ^ (expression_to_string e2) ^ ")"
	| Binop(Less, e1, e2) -> "(" ^ (expression_to_string e1) ^ ") < (" ^ (expression_to_string e2) ^ ")"
	| Binop(LessOrEqual, e1, e2) -> "(" ^ (expression_to_string e1) ^ ") <= (" ^ (expression_to_string e2) ^ ")"
	| Binop(Greater, e1, e2) -> "(" ^ (expression_to_string e1) ^ ") > (" ^ (expression_to_string e2) ^ ")"
	| Binop(GreaterOrEqual, e1, e2) -> "(" ^ (expression_to_string e1) ^ ") >= (" ^ (expression_to_string e2) ^ ")"
	| Binop(And, e1, e2) -> "(" ^ (expression_to_string e1) ^ ") and (" ^ (expression_to_string e2) ^ ")"
	| Binop(Or, e1, e2) -> "(" ^ (expression_to_string e1) ^ ") or (" ^ (expression_to_string e2) ^ ")"
	| Unop(Not, e1) -> "not(" ^ (expression_to_string e1) ^ ")"
	| Pair(e1, e2) -> "(" ^ (expression_to_string e1) ^ ", " ^ (expression_to_string e2) ^ ")"
	| Fst(e1) -> "fst(" ^ (expression_to_string e1) ^ ")"
	| Snd(e1) -> "snd(" ^ (expression_to_string e1) ^ ")"
	| If(e1, e2, e3) -> "if(" ^ (expression_to_string e1) ^ ") {" ^ (expression_to_string e2) ^ "} else {" ^ (expression_to_string e3) ^ "}"
	| Id(x) -> "id(" ^ x ^ ")"
	| App(e1, e2) -> "(" ^ (expression_to_string e1) ^ " " ^ (expression_to_string e2) ^ ")"
	| Fn(x, e1) -> "fn " ^ x ^ " in (" ^ (expression_to_string e1) ^ ")"
	| Let(x, e1, e2) -> "let " ^ x ^ " = (" ^ (expression_to_string e1) ^ ") in (" ^ (expression_to_string e2) ^ ")"
	| Letrec(x, y, e1, e2) -> "let rec " ^ x ^ " = fn " ^ y ^ "( " ^ (expression_to_string e1) ^ ") in (" ^ (expression_to_string e2) ^ ")"
	| Nil -> "Nil"
	| Cons(e1, e2) -> "cons(" ^ (expression_to_string e1) ^ ", " ^ (expression_to_string e2) ^ ")"
	| Hd(e) -> "hd(" ^ (expression_to_string e) ^ ")"
	| Tl(e) -> "tl(" ^ (expression_to_string e) ^ ")"
	| Isempty(e) -> "isempty(" ^ (expression_to_string e) ^ ")"
	| Raise -> "Raise"
	| Try(e1, e2) -> "try(" ^ (expression_to_string e1) ^ ") with (" ^ (expression_to_string e2) ^ ")"

(* Test eval *)
let rec run_rec equations_list n = match equations_list with
	| (e, correct_type)::tail -> 
		let type_e = typeinfer [] e in
		let s_type_e = type_to_string type_e in
		let s_type = type_to_string correct_type in
		(* let value = eval e in *)

		print_endline "";
		print_endline (string_of_int(n) ^ " =======================================");
		
		if (String.compare s_type_e s_type) != 0 then begin print_endline "======================== TYPE NOT CORRECT ========================"; exit(1); end
		else ();

		(* if value == v then 
			print_endline "TEST PASSED ===========================";
		else
			print_endline "TEST NOT PASSED ======================="; *)

		print_endline ("Expression: " ^ (expression_to_string e));
		print_endline ("Type: " ^ s_type_e);
		(* print_endline "Value: " ^ (value_to_string value); *)
		print_endline "";

		(run_rec tail (n + 1))

	| [] -> ();;

let run equations_list = run_rec equations_list 0

(* Run all *)
let es = [(e0, TypeInt);  (e1, TypeInt);  (e2, TypeBool);  (e3, TypeBool);  (e4, TypeInt);  
		  (e5, TypeInt);  (e6, TypeInt);  (e7, TypeInt);  (e8, TypeBool);  (e9, TypeBool);
	      (e10, TypeBool); (e11, TypeBool); (e12, TypeBool); (e13, TypeBool); (e14, TypeBool); 
	      (e15, TypeBool); (e16, TypeBool); (e17, TypeBool); (e18, TypeBool); (e19, TypeBool);
	      (e20, TypeBool); (e21, TypeBool); (e22, TypeBool); (e23, TypeBool); (e24, TypeBool); 
	      (e25, TypeBool); (e26, TypeBool); (e27, TypeBool); (e28, TypeBool); (e29, TypeBool);
	      (e30, TypePair(TypeInt, TypeInt)); (e31, TypeInt); (e32, TypeInt); (e33, TypeInt); (e34, TypeInt); (e35, TypeBool); 
	      (e36, TypeFn(TypeInt, TypeInt)); (e37, TypeInt); (e38, TypeInt); (e39, TypeInt);
	      (e40, TypeInt); (e41, TypeList(TypeInt)); (e42, TypeList(TypeInt)); (e43, TypeInt); (e44, TypeList(TypeInt)); (e45, TypeBool); 
	      (e46, TypeBool); (e47, TypeBool); (e48, TypeBool); (e49, TypeInt);
	      (e50, TypeBool); (e51, TypeBool)];;

print_endline "Running tests...";;
run es;;
