#indent "off"
module KNormal
(* give names to intermediate values (K-normalization) *)

type t = (* K³‹K‰»Œã‚ÌŽ® (caml2html: knormal_t) *)
  | Unit
  | Int of int
  | Float of float
  | Neg of Id.t
  | Add of Id.t * Id.t
  | Sub of Id.t * Id.t
	| Mul of Id.t * Id.t
	| Div of Id.t * Id.t
  | FNeg of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | IfEq of Id.t * Id.t * t * t (* ”äŠr + •ªŠò (caml2html: knormal_branch) *)
  | IfLE of Id.t * Id.t * t * t (* ”äŠr + •ªŠò *)
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | LetRec of fundef * t
  | App of Id.t * Id.t list
  | Tuple of Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | ExtArray of Id.t
  | ExtFunApp of Id.t * Id.t list
	(*’Ç‰Á*)
	| Print of Id.t
	| PrintShort of Id.t
	| Scan of Id.t
	| Sqrt of Id.t
and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

let rec fv = function (* Ž®‚ÉoŒ»‚·‚éiŽ©—R‚Èj•Ï” (caml2html: knormal_fv) *)
  | Unit | Int(_) | Float(_) | ExtArray(_) -> Set.empty
  | Neg(x) | FNeg(x) -> Set.singleton x
  | Add(x, y) | Sub(x, y) | Mul(x,y) | Div(x,y) | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) | Get(x, y) -> Set.ofList [x; y]
  | IfEq(x, y, e1, e2) | IfLE(x, y, e1, e2) -> Set.add x (Set.add y (Set.union (fv e1) (fv e2)))
  | Let((x, t), e1, e2) -> Set.union (fv e1) (Set.remove x (fv e2))
  | Var(x) -> Set.singleton x
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) ->
      let zs = Set.difference (fv e1) (Set.ofList (List.map fst yts)) in
      Set.difference (Set.union zs (fv e2)) (Set.singleton x)
  | App(x, ys) -> Set.ofList (x :: ys)
  | Tuple(xs) | ExtFunApp(_, xs) -> Set.ofList xs
  | Put(x, y, z) -> Set.ofList [x; y; z]
  | LetTuple(xs, y, e) -> Set.add y (Set.difference (fv e) (Set.ofList (List.map fst xs)))
	| Print(x) -> Set.singleton x
	| PrintShort(x) -> Set.singleton x
	| Scan(x) -> Set.singleton x
	| Sqrt(x) -> Set.singleton x

let insert_let (e, t) k = (* let‚ð‘}“ü‚·‚é•â•ŠÖ” (caml2html: knormal_insert) *)
  match e with
  | Var(x) -> k x
  | _ ->
      let x = Id.gentmp t in
      let e', t' = k x in
      Let((x, t), e, e'), t'

let rec g env = function (* K³‹K‰»ƒ‹[ƒ`ƒ“–{‘Ì (caml2html: knormal_g) *)
  | Syntax.Unit -> Unit, Type.Unit
  | Syntax.Bool(b) -> Int(if b then 1 else 0), Type.Int (* ˜_—’ltrue, false‚ð®”1, 0‚É•ÏŠ· (caml2html: knormal_bool) *)
  | Syntax.Int(i) -> Int(i), Type.Int
  | Syntax.Float(d) -> Float(d), Type.Float
  | Syntax.Not(e) -> g env (Syntax.If(e, Syntax.Bool(false), Syntax.Bool(true)))
  | Syntax.Neg(e) ->
      insert_let (g env e)
			(fun x -> Neg(x), Type.Int)
	| Syntax.Sqrt(e) ->
			insert_let (g env e)
			(fun x -> Sqrt(x), Type.Float)
  | Syntax.Add(e1, e2) -> (* ‘«‚µŽZ‚ÌK³‹K‰» (caml2html: knormal_add) *)
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> Add(x, y), Type.Int))
  | Syntax.Sub(e1, e2) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> Sub(x, y), Type.Int))
  | Syntax.Mul(e1, e2) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> Mul(x, y), Type.Int))
  | Syntax.Div(e1, e2) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> Div(x, y), Type.Int))
  | Syntax.FNeg(e) ->
      insert_let (g env e)
	(fun x -> FNeg(x), Type.Float)
  | Syntax.FAdd(e1, e2) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> FAdd(x, y), Type.Float))
  | Syntax.FSub(e1, e2) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> FSub(x, y), Type.Float))
  | Syntax.FMul(e1, e2) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> FMul(x, y), Type.Float))
  | Syntax.FDiv(e1, e2) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> FDiv(x, y), Type.Float))
  | Syntax.Eq _ | Syntax.LE _ as cmp ->
      g env (Syntax.If(cmp, Syntax.Bool(true), Syntax.Bool(false)))
  | Syntax.If(Syntax.Not(e1), e2, e3) -> g env (Syntax.If(e1, e3, e2)) (* not‚É‚æ‚é•ªŠò‚ð•ÏŠ· (caml2html: knormal_not) *)
  | Syntax.If(Syntax.Eq(e1, e2), e3, e4) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y ->
	      let e3', t3 = g env e3 in
	      let e4', t4 = g env e4 in
	      IfEq(x, y, e3', e4'), t3))
  | Syntax.If(Syntax.LE(e1, e2), e3, e4) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y ->
	      let e3', t3 = g env e3 in
	      let e4', t4 = g env e4 in
	      IfLE(x, y, e3', e4'), t3))
  | Syntax.If(e1, e2, e3) -> g env (Syntax.If(Syntax.Eq(e1, Syntax.Bool(false)), e3, e2)) (* ”äŠr‚Ì‚È‚¢•ªŠò‚ð•ÏŠ· (caml2html: knormal_if) *)
  | Syntax.Let((x, t), e1, e2) ->
      let e1', t1 = g env e1 in
      let e2', t2 = g (Map.add x t env) e2 in
      Let((x, t), e1', e2'), t2
  | Syntax.Var(x) when Map.containsKey x env -> Var(x), Map.find x env
  | Syntax.Var(x) -> (* ŠO•””z—ñ‚ÌŽQÆ (caml2html: knormal_extarray) *)
      (match Map.find x !Typing.extenv with
      | Type.Array(_) as t -> ExtArray x, t
      | _ -> failwith (Printf.sprintf "external variable %s does not have an array type" x))
  | Syntax.LetRec({ Syntax.name = (x, t); Syntax.args = yts; Syntax.body = e1 }, e2) ->
      let env' = Map.add x t env in
      let e2', t2 = g env' e2 in
      let e1', t1 = g (M.add_list yts env') e1 in
      LetRec({ name = (x, t); args = yts; body = e1' }, e2'), t2
  | Syntax.App(Syntax.Var(f), e2s) when not (Map.containsKey f env) -> (* ŠO•”ŠÖ”‚ÌŒÄ‚Ño‚µ (caml2html: knormal_extfunapp) *)
		(if f="print_char" 
		then
			(match e2s with
				| [x] -> 
					insert_let (g env x) (fun y -> Print(y), Type.Unit)
				| _ -> failwith "fatal error: print_char too many arguments")
		else( if f="input_char" 
		then
			(match e2s with
				| [x] -> 
					insert_let (g env x) (fun y -> Scan(y), Type.Int)
				| _ -> failwith "fatal error: input_char too many arguments")
		else( if f="print_short"
		then
			(match e2s with
				| [x] -> 
					insert_let (g env x) (fun y -> PrintShort(y), Type.Unit)
				| _ -> failwith "fatal error: print_short too many arguments")
		else
      (match Map.find f !Typing.extenv with
				| Type.Fun(_, t) ->
						let rec bind xs = 
							function (* "xs" are identifiers for the arguments *)
							| [] -> ExtFunApp(f, xs), t
							| e2 :: e2s -> insert_let (g env e2) (fun x -> bind (xs @ [x]) e2s) in
					  bind [] e2s (* left-to-right evaluation *)
		   | _ -> failwith "fatal error while processing Syntax.App (external call)")))
		)
  | Syntax.App(e1, e2s) ->
      (match g env e1 with
      | _, Type.Fun(_, t) as g_e1 ->
				insert_let g_e1
					(fun f ->
						let rec bind xs = function (* "xs" are identifiers for the arguments *)
							| [] -> App(f, xs), t
							| e2 :: e2s ->
								insert_let (g env e2)
									(fun x -> bind (xs @ [x]) e2s) in
							bind [] e2s) (* left-to-right evaluation *)
      | _ -> failwith "fatal error while processing Syntax.App (internal call)")
  | Syntax.Tuple(es) ->
      let rec bind xs ts = function (* "xs" and "ts" are identifiers and types for the elements *)
				| [] -> Tuple(xs), Type.Tuple(ts)
				| e :: es ->
						let _, t as g_e = g env e in
						insert_let g_e
							(fun x -> bind (xs @ [x]) (ts @ [t]) es) in
						bind [] [] es
  | Syntax.LetTuple(xts, e1, e2) ->
      insert_let (g env e1)
	(fun y ->
	  let e2', t2 = g (M.add_list xts env) e2 in
	  LetTuple(xts, y, e2'), t2)
  | Syntax.Array(e1, e2) ->
      insert_let (g env e1)
	(fun x ->
	  let _, t2 as g_e2 = g env e2 in
	  insert_let g_e2
	    (fun y ->
	      let l =
		match t2 with
		| Type.Float -> "create_float_array"
		| _ -> "create_array" in
	      ExtFunApp(l, [x; y]), Type.Array(t2)))
  | Syntax.Get(e1, e2) ->
      (match g env e1 with
      |	_, Type.Array(t) as g_e1 ->
	  insert_let g_e1
	    (fun x -> insert_let (g env e2)
		(fun y -> Get(x, y), t))
      | _ -> failwith "fatal error while processing Syntax.Get")
  | Syntax.Put(e1, e2, e3) ->
					insert_let (g env e1)
						(fun x -> insert_let (g env e2)
							(fun y -> insert_let (g env e3)
								(fun z -> Put(x,y,z), Type.Unit)))
(*  | Syntax.Put(e1, e2, e3) ->
		(match e3 with
			| Syntax.Tuple t ->
					let tree = g env e3 in 
					insert_let (g env e1) 
						(fun x -> (Change(x,changelist tree), Type.Unit))
			| _ -> 
					insert_let (g env e1)
						(fun x -> insert_let (g env e2)
							(fun y -> insert_let (g env e3)
								(fun z -> Put(x,y,z), Type.Unit)))
			)

let rec changelist tree = 
	match tree with
	| Let *)

let f e = fst (g Map.empty e)
