#indent "off"
module Closure
type closure = { entry : Id.l; actual_fv : Id.t list }
type t = (* クロージャ変換後の式 (caml2html: closure_t) *)
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
  | IfEq of Id.t * Id.t * t * t
  | IfLE of Id.t * Id.t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | MakeCls of (Id.t * Type.t) * closure * t
  | AppCls of Id.t * Id.t list
  | AppDir of Id.l * Id.t list
  | Tuple of Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | ExtArray of Id.l
	(*追加*)
	| Print of Id.t
	| PrintShort of Id.t
	| Scan of Id.t
	| Sqrt of Id.t
type fundef = { name : Id.l * Type.t;
		args : (Id.t * Type.t) list;
		formal_fv : (Id.t * Type.t) list;
		body : t }
type prog = Prog of fundef list * t

let rec fv arg = 
	match arg with
  | Unit | Int(_) | Float(_) | ExtArray(_) -> Set.empty
  | Neg(x) | FNeg(x) | Print(x) | PrintShort(x) | Scan(x) | Sqrt(x) -> Set.singleton x
  | Add(x, y) | Sub(x, y) | Mul(x,y) | Div(x,y) | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) | Get(x, y) -> Set.ofList [x; y]
  | IfEq(x, y, e1, e2)| IfLE(x, y, e1, e2) -> Set.add x (Set.add y (Set.union (fv e1) (fv e2)))
  | Let((x, t), e1, e2) -> Set.union (fv e1) (Set.remove x (fv e2))
  | Var(x) -> Set.singleton x
  | MakeCls((x, t), { entry = l; actual_fv = ys }, e) -> Set.remove x (Set.union (Set.ofList ys) (fv e))
  | AppCls(x, ys) -> Set.ofList (x :: ys)
  | AppDir(_, xs) | Tuple(xs) -> Set.ofList xs
  | LetTuple(xts, y, e) -> Set.add y (Set.difference (fv e) (Set.ofList (List.map fst xts)))
  | Put(x, y, z) -> Set.ofList [x; y; z];;

let toplevel : fundef list ref = ref []

let rec g env known arg = (* クロージャ変換ルーチン本体 (caml2html: closure_g) *)
	match arg with
  | KNormal.Unit -> Unit
  | KNormal.Int(i) -> Int(i)
  | KNormal.Float(d) -> Float(d)
  | KNormal.Neg(x) -> Neg(x)
  | KNormal.Add(x, y) -> Add(x, y)
  | KNormal.Sub(x, y) -> Sub(x, y)
  | KNormal.Mul(x, y) -> Mul(x, y)
  | KNormal.Div(x, y) -> Div(x, y)
  | KNormal.FNeg(x) -> FNeg(x)
  | KNormal.FAdd(x, y) -> FAdd(x, y)
  | KNormal.FSub(x, y) -> FSub(x, y)
  | KNormal.FMul(x, y) -> FMul(x, y)
  | KNormal.FDiv(x, y) -> FDiv(x, y)
  | KNormal.IfEq(x, y, e1, e2) -> IfEq(x, y, g env known e1, g env known e2)
  | KNormal.IfLE(x, y, e1, e2) -> IfLE(x, y, g env known e1, g env known e2)
  | KNormal.Let((x, t), e1, e2) -> Let((x, t), g env known e1, g (Map.add x t env) known e2)
  | KNormal.Var(x) -> Var(x)
  | KNormal.LetRec({ KNormal.name = (f, t); KNormal.args = xts; KNormal.body = e1 }, e2) -> (* 関数定義の場合 (caml2html: closure_letrec) *)
      (* 関数定義let rec f x1 ... xn = e1 in e2の場合は、
	 fに自由変数がない(closureを介さずdirectに呼び出せる)
	 と仮定し、knownに追加してe1をクロージャ変換してみる *)
      let toplevel_backup = !toplevel in
      let env' = Map.add f t env in
      let known' = Set.add f known in
      let e1' = g (M.add_list xts env') known' e1 in
      (* 本当に自由変数がなかったか、変換結果e1'を確認する *)
      (* 注意: e1'にx自身が変数として出現する場合はclosureが必要!
         (thanks to nuevo-namasute and azounoman; test/cls-bug2.ml参照) *)
      let zs = Set.difference (fv e1') (Set.ofList (List.map fst xts)) in
      let known', e1' =
				if Set.isEmpty zs then known', e1' else
				(* 駄目だったら状態(toplevelの値)を戻して、クロージャ変換をやり直す *)
				(Printf.eprintf "free variable(s) %s found in function %s\n" (Id.pp_list (Set.toList zs)) f;
				 Printf.eprintf "function %s cannot be directly applied in fact\n" f;
				 toplevel := toplevel_backup;
				 let e1' = g (M.add_list xts env') known e1 in
				 known, e1') in
						let zs = Set.toList (Set.difference (fv e1') (Set.add f (Set.ofList (List.map fst xts)))) in (* 自由変数のリスト *)
						let zts = List.map (fun z -> (z, Map.find z env')) zs in (* ここで自由変数zの型を引くために引数envが必要 *)
						toplevel := { name = (Id.L(f), t); args = xts; formal_fv = zts; body = e1' } :: !toplevel; (* トップレベル関数を追加 *)
						let e2' = g env' known' e2 in
						if Set.contains f (fv e2') then (* xが変数としてe2'に出現するか *)
							MakeCls((f, t), { entry = Id.L(f); actual_fv = zs }, e2') (* 出現していたら削除しない *)
									else
										(Printf.eprintf "eliminating closure(s) %s\n" f;
										 e2') (* 出現しなければMakeClsを削除 *)
  | KNormal.App(x, ys) when Set.contains x known -> (* 関数適用の場合 (caml2html: closure_app) *)
      Printf.eprintf "directly applying %s\n" x;
      AppDir(Id.L(x), ys)
  | KNormal.App(f, xs) -> AppCls(f, xs)
  | KNormal.Tuple(xs) -> Tuple(xs)
  | KNormal.LetTuple(xts, y, e) -> LetTuple(xts, y, g (M.add_list xts env) known e)
  | KNormal.Get(x, y) -> Get(x, y)
  | KNormal.Put(x, y, z) -> Put(x, y, z)
  | KNormal.ExtArray(x) -> ExtArray(Id.L(x))
  | KNormal.ExtFunApp(x, ys) -> AppDir(Id.L("external_" ^ x), ys)
	| KNormal.Print(x) -> Print(x)
	| KNormal.PrintShort(x) -> PrintShort(x)
	| KNormal.Scan(x) -> Scan(x)
	| KNormal.Sqrt(x) -> Sqrt(x);;

let f e =
  toplevel := [];
  let e' = g Map.empty Set.empty e in
  Prog(List.rev !toplevel, e')
