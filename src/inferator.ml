open definitions
open exceptions
open utils

let rec collect_rec (environment: typeEnv) (program: expression) (varGen: newVarGenerator) = match program with
	| Nval(val) -> (TypeInt, [], varGen)

	| Bval(val) -> (TypeBool, [], varGen)

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

	(* | Fst(e) -> como definir a regra *)

	(* | Snd(e) -> como definir a regra *)

	| If(e1, e2, e3) ->
		let (type1, eq1, gen1) = collect_rec environment e1 varGen in
		let (type2, eq2, gen2) = collect_rec environment e2 gen1 in
		let (type3, eq3, gen3) = collect_rec environment e3 gen2 in
		let new_eq = [(type1, TypeBool); (type2, type3)] in
		(type2, List.concat [eq1; eq2; eq3; new_eq], gen3)

	| Id(var) -> 
		(try 
			(let typeT = lookup environment var in
			(typeT, [], varGen))
		with
			_ -> raise (VariableNotFound "Variable not found in environment"))

	| App(e1, e2) ->
		let (type1, eq1, gen1) = collect_rec environment e1 varGen in
		let (type2, eq2, gen2) = collect_rec environment e2 gen1 in
		let NewVariable(newVar, newGen) = gen2 () in 
		let x = TypeId(newVar) in
		let new_eq = [(type1, TypeFn(type2, x))] in
		(x, List.concat [eq1; eq2; new_eq], newGen)

	| Fn(var, e) ->
		let NewVariable(newVar, newGen) = varGen () in 
		let x = TypeId(newVar) in
		let (type1, eq1, gen1) = collect_rec List.concat [environment; [(var, x)]] e newGen in
		(TypeFn(x, type1), eq1, gen1)

	| Let(var, e1, e2) ->
		let NewVariable(newVar, newGen) = varGen () in 
		let x = TypeId(newVar) in
		let (type1, eq1, gen1) = collect_rec environment e1 newGen in
		let (type2, eq2, gen2) = collect_rec List.concat [environment; [(var, x)]] e2 gen1 in
		let new_eq = [(x, type1)] in
		(type2, List.concat [eq1; eq2; new_eq], gen2)

	| Letrec(var1, var2, e1, e2) ->
		let NewVariable(newVar1, newGen1) = varGen () in 
		let x = TypeId(newVar1) in
		let NewVariable(newVar2, newGen2) = newGen1 () in 
		let y = TypeId(newVar2) in
		let (type1, eq1, gen1) = collect_rec List.concat [environment; [(var1, x), (var2, y)]] e1 newGen2 in
		let (type2, eq2, gen2) = collect_rec List.concat [environment; [(var1, x)]] e2 gen1 in
		let new_eq = [(x, TypeFn(y, type1))] in
		(type2, List.concat [eq1; eq2; new_eq], gen2)

	| Nil -> 
		let NewVariable(newVar, newGen) = varGen () in 
		let x = TypeId(newVar) in 
		(TypeList(x), [], newGen)

	| Cons(e1, e2) ->
		let (type1, eq1, gen1) = collect_rec environment e1 varGen in
		let (type2, eq2, gen2) = collect_rec environment e2 gen2 in
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

	| Raise -> 
		let NewVariable(newVar, newGen) = varGen () in 
		let x = TypeId(newVar) in 
		(x, [], newGen)

	| Try(e1, e2) -> 
		let (type1, eq1, gen1) = collect_rec environment e1 varGen in
		let (type2, eq2, gen2) = collect_rec environment e2 gen1 in
		let new_eq = [(type1, type2)] in
		(type2, List.concat [eq1; eq2; new_eq], gen2)

let collect (environment: typeEnv) (program: expression) = collect_rec environment program varGenerator

let typeinfer (environment: typeEnv) (program: expression) : typeDef = 
	let (types, type_equations, varGen) = collect environment program in
	let unification = unify [] type_equations in
	applysubs unification types
