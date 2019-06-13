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

	| Fst(e) -> 
		let NewVariable(newVar1, newGen1) = varGen () in 
		let NewVariable(newVar2, newGen2) = newGen1 () in 
		let (type1, eq1, gen3) = collect_rec environment e newGen2 in
		let x = TypeId(newVar1) in
		let y = TypeId(newVar2) in
		let new_eq = [(type1, TypePair(x, y))]
		(x, List.concat [eq1; new_eq], gen3)

	| Snd(e) -> como definir a regra
		let NewVariable(newVar1, newGen1) = varGen () in 
		let NewVariable(newVar2, newGen2) = newGen1 () in 
		let (type1, eq1, gen3) = collect_rec environment e newGen2 in
		let x = TypeId(newVar1) in
		let y = TypeId(newVar2) in
		let new_eq = [(type1, TypePair(x, y))]
		(y, List.concat [eq1; new_eq], gen3)

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
			_ -> raise (VariableError "Variable not found in environment"))

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
		let new_eq = [(type1, type2)] in
		(type2, List.concat [eq1; eq2; new_eq], gen2)

let collect (environment: typeEnv) (program: expression) = collect_rec environment program varGenerator

let rec occur_check_rec (x: string) (t: typeDef) : bool = match t with
	| TypeInt -> false
	| TypeBool -> false
	| TypeId(y) -> (y = x)
	| TypeList(t1) -> occur_check_rec t1
	| TypeFn(t1, t2) -> occur_check_rec t1 || occur_check_rec t2
	| TypePair(t1, t2) -> occur_check_rec t1 || occur_check_rec t2

let occur_check (x: string) (t: typeDef) : bool = occur_check_rec x t

let rec typesub_rec (x: string) (t1: typeDef) (t2: typeDef) : typeDef = match t2 with
	| TypeInt -> TypeInt

	| TypeBool -> TypeBool

	| TypeId(y) -> if occur_check x (TypeId(y)) then t1 else TypeId(y)
	
	| TypeList(t) -> let new_type = typesub_rec x t1 t in TypeList(new_type)
	
	| TypeFn(t3, t4) -> 
		let new_type3 = typesub_rec x t1 t3 in
		let new_type4 = typesub_rec x t1 t4 in
		TypeFn(new_type3, new_type4)

	| TypePair(t3, t4) -> 
		let new_type3 = typesub_rec x t1 t3 in
		let new_type4 = typesub_rec x t1 t4 in
		TypePair(new_type3, new_type4)

let typesub (x: string) (t1: typeDef) (t2: typeDef) : typeDef = typesub_rec x t1 t2

let typesub_equation_rec (x: string) (t: typeDef) (type_equations: typeEquations) : typeEquations = match type_equations with
	| [] -> []
	| (t1, t2) :: c -> List.append [(typesub x t t1, typesub x t t2)] (typesub_rec x t c)

let typesub_equation (x: string) (t: typeDef) (type_equations: typeEquations) : typeEquations = typesub_equation_rec x t type_equations

let rec unify_rec (type_equations: typeEquations) : typeEquations = match type_equations with
	| [] -> []

	| (TypeInt, TypeInt) :: c -> unify_rec c

	| (TypeBool, TypeBool) :: c -> unify_rec c

	| (TypeList(t1), TypeList(t2)) :: c ->  unify_rec ((t1, t2) :: c)

	| (TypeFn(t1, t2), TypeFn(t3, t4)) :: c -> unify_rec ((t1, t3) :: (t2, t4) :: c)

	| (TypePair(t1, t2), TypePair(t3, t4)) :: c -> unify_rec ((t1, t3) :: (t2, t4) :: c)

	| (TypeId(x), TypeId(x)) :: c -> unify_rec c

	| (TypeId(x), t) :: c ->
		if occur_check x t then
			raise (UnifyError "x occurs in t.")
		else
			let substitutions = typesub_equation x t c in
			let new_unification = unify_rec substitutions in
			List.concat [new_unification; (TypeId(x), t)]

	| (t, TypeId(x)) :: c -> 
		if occur_check x t then
			raise (UnifyError "x occurs in t.")
		else
			let substitutions = typesub_equation x t c in
			let new_unification = unify_rec substitutions in
			List.concat [new_unification; (TypeId(x), t)]

	| (_, _) :: c -> raise (UnifyError "Cannot solve type equations.")

let unify (type_equations: typeEquations) : typeEquations = unify_rec type_equations

let rec applysubs_rec (type_equations: typeEquations) (t: typeDef) : typeDef = match type_equations with
	| [] -> []
	| (TypeId(x), t1) :: c -> List.append [typesub x t1 t] (applysubs_rec c t)

let applysubs (type_equations: typeEquations) (t: typeDef) : typeDef = applysubs_rec type_equations t

let typeinfer (environment: typeEnv) (program: expression) : typeDef = 
	let (prog_type, type_equations, varGen) = collect environment program in
	let unification = unify type_equations in
	applysubs unification prog_type
