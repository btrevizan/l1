(* ================================================================================================================== *)
(* ================================================================================================================== *)
(* Definitions *)
(* ================================================================================================================== *)
(* ================================================================================================================== *)
type variable = string

type newVariable = NewVariable of string * newVarGenerator and newVarGenerator = unit -> newVariable

type typeDef = TypeInt 
			| TypeBool 
			| TypeId of string 
			| TypeFn of typeDef * typeDef 
			| TypeList of typeDef
			| TypePair of typeDef * typeDef
			| TypeUndefined (* only for tests *)

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

type value = ValueNum of int
			| ValueBool of bool
			| ValueNil 
			| ValueCons of value * value
			| ValueRaise
			| ValuePair of value * value
			| ValueFn of variable * expression * env and env = (variable * value) list

type typeEnv = (variable * typeDef) list

type typeEquations = (typeDef * typeDef) list

(* ================================================================================================================== *)
(* ================================================================================================================== *)
(* Exceptions *)
(* ================================================================================================================== *)
(* ================================================================================================================== *)
exception VariableError of string
exception OperationError of string
exception UnifyError of string

(* ================================================================================================================== *)
(* ================================================================================================================== *)
(* Utils *)
(* ================================================================================================================== *)
(* ================================================================================================================== *)
let rec generator n () = NewVariable("#x" ^ string_of_int n, generator (n + 1))
let varGenerator = generator 0

let rec lookup environment x = match environment with
	| (y, v)::tail -> if (String.compare y x) == 0 then v else (lookup tail x)
	| [] -> raise (VariableError("Variable not found in environment"))

(* ================================================================================================================== *)
(* ================================================================================================================== *)
(* Inferator *)
(* ================================================================================================================== *)
(* ================================================================================================================== *)
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

(* ================================================================================================================== *)
(* ================================================================================================================== *)
(* Bigstep *)
(* ================================================================================================================== *)
(* ================================================================================================================== *)
let rec eval_rec (environment: env) (e: expression) : value = match e with
	| Nval(n) -> ValueNum(n)

	| Bval(n) -> ValueBool(n)

	| Binop(op, e1, e2) ->
		let n1 = eval_rec environment e1 in (
			match n1 with
			| ValueRaise -> ValueRaise
			| _ ->
				let n2 = eval_rec environment e2 in (
					match (op, n1, n2) with
						| (_, _, ValueRaise) -> ValueRaise
						| (Sum, ValueNum(n1), ValueNum(n2)) -> ValueNum(n1 + n2)
						| (Sub, ValueNum(n1), ValueNum(n2)) -> ValueNum(n1 - n2)
						| (Mult, ValueNum(n1), ValueNum(n2)) -> ValueNum(n1 * n2)
						| (Div, ValueNum(n1), ValueNum(n2)) -> if n2 != 0 then ValueNum(n1 / n2) else ValueRaise
						| (Equal, ValueNum(n1), ValueNum(n2)) -> ValueBool(n1 == n2)
						| (Diff, ValueNum(n1), ValueNum(n2)) -> ValueBool(n1 != n2)
						| (Less, ValueNum(n1), ValueNum(n2)) -> ValueBool(n1 < n2)
						| (LessOrEqual, ValueNum(n1), ValueNum(n2)) -> ValueBool(n1 <= n2)
						| (Greater, ValueNum(n1), ValueNum(n2)) -> ValueBool(n1 > n2)
						| (GreaterOrEqual, ValueNum(n1), ValueNum(n2)) -> ValueBool(n1 >= n2)
						| (And, ValueBool(n1), ValueBool(n2)) -> ValueBool(n1 && n2)
						| (Or, ValueBool(n1), ValueBool(n2)) -> ValueBool(n1 || n2)
						| (_, _, _) -> raise (OperationError "Operation not found.")
				)
		)

	| Unop(op, e1) ->
		let n1 = eval_rec environment e1 in (
		match (op, n1) with
			| (_, ValueRaise) -> ValueRaise
			| (Not, ValueBool(n1)) -> ValueBool(not n1)
			| (_, _) -> raise (OperationError "Operation not found.")
		)

	| Pair(e1, e2) ->
		let n1 = eval_rec environment e1 in (
			match n1 with
			| ValueRaise -> ValueRaise
			| _ -> 
				let n2 = eval_rec environment e2 in (
					match (n1, n2) with
						| (_, ValueRaise) -> ValueRaise
						| (_, _) -> ValuePair(n1, n2)
				)
		)

	| Fst(e1) ->
		let n1 = eval_rec environment e1 in (
			match n1 with
				| ValueRaise -> ValueRaise
				| ValuePair(n11, n12) -> n11
				| _ -> raise (OperationError "Operation not found.")
		)
	
	| Snd(e1) ->
		let n1 = eval_rec environment e1 in (
			match n1 with
				| ValueRaise -> ValueRaise
				| ValuePair(n11, n12) -> n12
				| _ -> raise (OperationError "Operation not found.")
		)

	| If(e1, e2,  e3) ->
		let n1 = eval_rec environment e1 in (
			match n1 with
				| ValueRaise -> ValueRaise
				| ValueBool(true) -> eval_rec environment e2
				| ValueBool(false) -> eval_rec environment e3
				| _ -> raise (OperationError "Operation not found.")
		)

	| Id(x) -> lookup environment x

	| App(e1, e2) ->
		let n1 = eval_rec environment e1 in (
			match n1 with
			| ValueRaise -> ValueRaise
			| _ -> 
				let n2 = eval_rec environment e2 in (
					match (n1, n2) with
						| (_, ValueRaise) -> ValueRaise
						| (ValueFn(x, f, f_env), n) -> eval_rec ((x,n)::f_env) f
						| (_, _) -> raise (OperationError "Operation not found.")
				)
		)
	
	| Fn(x, e1) -> ValueFn(x, e1, environment)
	
	| Let(x, e1, e2) ->
		let n1 = eval_rec environment e1 in (
		match n1 with
			| ValueRaise -> ValueRaise
			| _ -> eval_rec ((x, n1)::environment) e2
		)

	| Letrec(f, y, e1, e2) -> 
		let alpha' = ValueFn(y, Letrec(f, y, e1, e1), environment) in
		eval_rec ((f, alpha')::environment) e2

	| Nil -> ValueNil
	
	| Cons(e1, e2) ->
		let n1 = eval_rec environment e1 in (
			match n1 with
			| ValueRaise -> ValueRaise
			| _ ->
				let n2 = eval_rec environment e2 in (
					match (n1, n2) with
						| (_, ValueRaise) -> ValueRaise
						| (_, _) -> ValueCons(n1, n2)
				)
		)
	
	| Hd(e1) -> 
		let n1 = eval_rec environment e1 in (
			match n1 with
				| ValueRaise -> ValueRaise
				| ValueNil -> ValueRaise
				| ValueCons(n11, _) -> n11
				| _ -> raise (OperationError "Operation not found.")
		)

	| Tl(e1) ->
		let n1 = eval_rec environment e1 in (
			match n1 with
				| ValueRaise -> ValueRaise
				| ValueNil -> ValueRaise
				| ValueCons(_, n12) -> n12
				| _ -> raise (OperationError "Operation not found.")
		)
	
	| Isempty(e1) ->
		let n1 = eval_rec environment e1 in (
			match n1 with
				| ValueRaise -> ValueRaise
				| ValueNil -> ValueBool(true)
				| ValueCons(l1, l2) -> ValueBool(false)
				| _ -> raise (OperationError "Operation not found.")
		)
	
	| Raise -> ValueRaise
	
	| Try(e1, e2) ->
		let n1 = eval_rec environment e1 in (
			match n1 with
				| ValueRaise -> eval_rec environment e2
				| _ -> n1
		)

let eval (e: expression) : value = eval_rec [] e

(* ================================================================================================================== *)
(* ================================================================================================================== *)
(* Tests *)
(* ================================================================================================================== *)
(* ================================================================================================================== *)
(* Test cases that should execute normally *)
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
					If(Binop(Equal, Id("x"), Nval(1)),
						Nval(1),
						Binop(Sum, 
                    		  App(Id("fibonacci"), Binop(Sub, Id("x"), Nval(1))),
                    	  	  App(Id("fibonacci"), Binop(Sub, Id("x"), Nval(2)))))
                    ), 
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

let e52 = Fn("var_test4", App(Id("var_test4"), App(Id("var_test4"), Nval(3))))
let e53 = Fn("var_test5", App(Id("var_test5"), App(Id("var_test5"), Bval(true))))
let e54 = Fn("var_test7", App(Id("var_test7"), Nval(3)))
let e55 = Fn("var_test8", Id("var_test8"))

let e56 = Letrec("sum", "l",
				 If(Isempty(Id("l")),
				    Nval(0),
				    Binop(Sum, 
				    	  Hd(Id("l")), 
				    	  App(Id("sum"), Tl(Id("l"))))	
				 ),
				 App(Id("sum"), e41))

let e57 = Letrec("mult", "l",
				 If(Isempty(Id("l")),
				    Nval(1),
				    Binop(Mult, 
				    	  Hd(Id("l")), 
				    	  App(Id("mult"), Tl(Id("l"))))	
				 ),
				 App(Id("mult"), e42))

let e58 = Letrec("all", "l",
				 If(Isempty(Id("l")),
				    Bval(true),
				    Binop(And, 
				    	  Hd(Id("l")), 
				    	  App(Id("all"), Tl(Id("l"))))	
				 ),
				 App(Id("all"), Cons(Bval(true), Cons(Bval(true), Cons(Bval(true), Cons(Bval(true), Nil))))))

let e59 = Letrec("all", "l",
				 If(Isempty(Id("l")),
				    Bval(true),
				    Binop(And, 
				    	  Hd(Id("l")), 
				    	  App(Id("all"), Tl(Id("l"))))	
				 ),
				 App(Id("all"), Cons(Bval(true), Cons(Bval(false), Cons(Bval(true), Nil)))))

(* Test cases that shouldn't execute normally *)
let w0 = Fn("var_test6", App(Id("var_test6"), Pair(App(Id("var_test6"), Nval(3)), App(Id("var_test6"), Nval(3)))))
let w1 = Let("var_test9", Fn("var_test10", Id("var_test10")), Pair(App(Id("var_test9"), Nval(3)), App(Id("var_test9"), Bval(true))))
let w2 = Cons(Nval(1), Cons(Bval(true), Cons(Nval(3), Nil)))
let w3 = Letrec("all", "l", If(Isempty(Id("l")), Bval(true), Binop(Mult, Hd(Id("l")), App(Id("all"), Tl(Id("l"))))), App(Id("all"), Cons(Bval(true), Cons(Bval(true), Cons(Bval(true), Cons(Bval(true), Nil))))))


(* Utils *)
let rec type_to_string (t: typeDef) : string = match t with
    | TypeInt -> "Integer"
	| TypeBool -> "Boolean"
    | TypeId(x) -> "id(" ^ x ^ ")"
	| TypeFn(t1, t2) -> "(" ^ (type_to_string t1) ^ ") -> (" ^ (type_to_string t2) ^ ")"
	| TypeList(t1) -> "List of " ^ (type_to_string t1)
    | TypePair(t1, t2) -> "(" ^ (type_to_string t1) ^ ", " ^ (type_to_string t1) ^ ")"
    | TypeUndefined -> "Undefined"

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
	| Fn(x, e1) -> "fn " ^ x ^ " -> (" ^ (expression_to_string e1) ^ ")"
	| Let(x, e1, e2) -> "let " ^ x ^ " = (" ^ (expression_to_string e1) ^ ") in (" ^ (expression_to_string e2) ^ ")"
	| Letrec(x, y, e1, e2) -> "let rec " ^ x ^ " = fn " ^ y ^ "( " ^ (expression_to_string e1) ^ ") in (" ^ (expression_to_string e2) ^ ")"
	| Nil -> "Nil"
	| Cons(e1, e2) -> "cons(" ^ (expression_to_string e1) ^ ", " ^ (expression_to_string e2) ^ ")"
	| Hd(e) -> "hd(" ^ (expression_to_string e) ^ ")"
	| Tl(e) -> "tl(" ^ (expression_to_string e) ^ ")"
	| Isempty(e) -> "isempty(" ^ (expression_to_string e) ^ ")"
	| Raise -> "Raise"
	| Try(e1, e2) -> "try(" ^ (expression_to_string e1) ^ ") with (" ^ (expression_to_string e2) ^ ")"

let rec value_to_string (v: value) : string = match v with
    | ValueNum(n) -> string_of_int(n)
	| ValueBool(b) -> string_of_bool(b)
	| ValueNil -> "ValueNil"
	| ValueCons(v1, v2) -> "cons(" ^ (value_to_string v1) ^ ", " ^ (value_to_string v2) ^ ")"
	| ValueRaise -> "Raise"
	| ValuePair(v1, v2) -> "(" ^ (value_to_string v1) ^ ", " ^ (value_to_string v2) ^ ")"
	| ValueFn(x, e1, _) -> "fn (" ^ x ^ ") = " ^ (expression_to_string e1)

(* Test eval *)
let es = [(e0, TypeInt, ValueNum(5));
		  (e1, TypeInt, ValueNum(10));  
		  (e2, TypeBool, ValueBool(true));  
		  (e3, TypeBool, ValueBool(false));  
		  (e4, TypeInt, ValueNum(15));  
		  (e5, TypeInt, ValueNum(5));  
		  (e6, TypeInt, ValueNum(50));  
		  (e7, TypeInt, ValueNum(2));  
		  (e8, TypeBool, ValueBool(false));  
		  (e9, TypeBool, ValueBool(true));
	      (e10, TypeBool, ValueBool(true)); 
	      (e11, TypeBool, ValueBool(false)); 
	      (e12, TypeBool, ValueBool(false)); 
	      (e13, TypeBool, ValueBool(false)); 
	      (e14, TypeBool, ValueBool(true)); 
	      (e15, TypeBool, ValueBool(true)); 
	      (e16, TypeBool, ValueBool(false)); 
	      (e17, TypeBool, ValueBool(true)); 
	      (e18, TypeBool, ValueBool(false)); 
	      (e19, TypeBool, ValueBool(true));
	      (e20, TypeBool, ValueBool(false)); 
	      (e21, TypeBool, ValueBool(true)); 
	      (e22, TypeBool, ValueBool(true)); 
	      (e23, TypeBool, ValueBool(false)); 
	      (e24, TypeBool, ValueBool(true)); 
	      (e25, TypeBool, ValueBool(false)); 
	      (e26, TypeBool, ValueBool(true)); 
	      (e27, TypeBool, ValueBool(true)); 
	      (e28, TypeBool, ValueBool(false)); 
	      (e29, TypeBool, ValueBool(true));
	      (e30, TypePair(TypeInt, TypeInt), ValuePair(ValueNum(5), ValueNum(10))); 
	      (e31, TypeInt, ValueNum(5)); 
	      (e32, TypeInt, ValueNum(10)); 
	      (e33, TypeInt, ValueNum(5)); 
	      (e34, TypeInt, ValueNum(10)); 
	      (e35, TypeBool, ValueBool(true)); 
	      (e36, TypeFn(TypeInt, TypeInt), ValueFn("var_teste1", Binop(Sum, Id("var_teste1"), Nval(5)), [])); 
	      (e37, TypeInt, ValueNum(15)); 
	      (e38, TypeInt, ValueNum(25)); 
	      (e39, TypeInt, ValueNum(120));
	      (e40, TypeInt, ValueNum(55)); 
	      (e41, TypeList(TypeInt), ValueCons(ValueNum(1), ValueCons(ValueNum(2), ValueCons(ValueNum(3), ValueNil)))); 
	      (e42, TypeList(TypeInt), ValueCons(ValueNum(5), ValueCons(ValueNum(2), ValueCons(ValueNum(15), ValueNil)))); 
	      (e43, TypeInt, ValueNum(1)); 
	      (e44, TypeList(TypeInt), ValueCons(ValueNum(2), ValueCons(ValueNum(3), ValueNil))); 
	      (e45, TypeBool, ValueBool(false)); 
	      (e46, TypeBool, ValueBool(true)); 
	      (e47, TypeBool, ValueBool(false));
	      (e48, TypeBool, ValueBool(false)); 
	      (e49, TypeInt, ValueBool(true));
	      (e50, TypeBool, ValueBool(true)); 
	      (e51, TypeBool, ValueBool(false));
	      (e52, TypeFn(TypeFn(TypeInt, TypeInt), TypeInt), ValueFn("var_test4", App(Id("var_test4"), App(Id("var_test4"), Nval(3))), []));
	      (e53, TypeFn(TypeFn(TypeBool, TypeBool), TypeBool), ValueFn("var_test5", App(Id("var_test5"), App(Id("var_test5"), Bval(true))), []));
	      (e54, TypeFn(TypeFn(TypeInt, TypeId("#x1")), TypeId("#x1")), ValueFn("var_test7", App(Id("var_test7"), Nval(3)), []));
	      (e55, TypeFn(TypeId("#x0"), TypeId("#x0")), ValueFn("var_test8", Id("var_test8"), []));
	      (e56, TypeInt, ValueNum(6));
	      (e57, TypeInt, ValueNum(150));
	      (e58, TypeBool, ValueBool(true));
	      (e59, TypeBool, ValueBool(false))];;

let ws = [w0; w1; w2; w3];;

let rec run_right_rec equations_list n = match equations_list with
	| (e, correct_type, correct_value)::tail -> 
		let type_e = typeinfer [] e in
		let s_type_e = type_to_string type_e in
		let s_type = type_to_string correct_type in

		print_endline "";
		print_endline (string_of_int(n) ^ " =======================================");
		print_endline ("Expression: " ^ (expression_to_string e));
		print_endline ("Type: " ^ s_type_e);

		if (String.compare s_type_e s_type) != 0 then begin print_endline "======================== TYPE NOT CORRECT ========================"; exit(1); end
		else ();

		let value = eval e in
		let s_value_e = value_to_string value in
		let s_value = value_to_string correct_value in 

		print_endline ("Value: " ^ s_value_e);
		print_endline "";
		
		if (String.compare s_value_e s_value) != 0 then begin print_endline "======================== VALUE NOT CORRECT ========================"; exit(1); end
		else ();

		(run_right_rec tail (n + 1))

	| [] -> ();;

let run_right equations_list = run_right_rec es 0

let rec run_wrong_rec equations_list n = match equations_list with
	| e::tail -> 
		let new_n = n + 1 in 
		
		print_endline "";
		print_endline (string_of_int(n) ^ " =======================================");

		let type_e = try typeinfer [] e with (UnifyError err) -> TypeUndefined in
		let s_type_e = type_to_string type_e in

		print_endline ("Expression: " ^ (expression_to_string e));
		print_endline ("Type: " ^ s_type_e);

		if (String.compare s_type_e "Undefined") != 0 then begin print_endline "======================== ERROR ========================"; exit(1); end
		else ();

		(run_wrong_rec tail new_n)

	| [] -> ();;

let run_wrong equations_list = run_wrong_rec ws 0
