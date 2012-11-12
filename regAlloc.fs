#indent "off"
module RegAlloc
open Asm

(* for register coalescing *)
(* [XXX] Call����������A���������͖��Ӗ��Ƃ������t���ʂȂ̂Œǂ�Ȃ��B
         ���̂��߂ɁuCall�����������ǂ����v��Ԃ�l�̑�1�v�f�Ɋ܂߂�B *)
let rec target' src (dest, t) = function
  | Mr(x) when x = src && is_reg dest ->
      assert (t <> Type.Unit);
      assert (t <> Type.Float);
      false, [dest]
  | FMr(x) when x = src && is_reg dest ->
      assert (t = Type.Float);
      false, [dest]
  | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2) | IfGE(_, _, e1, e2)
  | IfFEq(_, _, e1, e2) | IfFLE(_, _, e1, e2) ->
      let c1, rs1 = target src (dest, t) e1 in
      let c2, rs2 = target src (dest, t) e2 in
      c1 && c2, rs1 @ rs2
  | CallCls(x, ys, zs) ->
      true, (target_args src regs 0 ys @
	     target_args src fregs 0 zs @
             if x = src then [reg_cl] else [])
  | CallDir(_, ys, zs) ->
      true, (target_args src regs 0 ys @
	     target_args src fregs 0 zs)
  | _ -> false, []
and target src dest = function (* register targeting (caml2html: regalloc_target) *)
  | Ans(exp) -> target' src dest exp
  | Let(xt, exp, e) ->
      let c1, rs1 = target' src xt exp in
      if c1 then true, rs1 else
      let c2, rs2 = target src dest e in
      c2, rs1 @ rs2
and target_args src all n = function (* auxiliary function for Call *)
  | [] -> []
  | y :: ys when src = y -> all.[n] :: target_args src all (n + 1) ys
  | _ :: ys -> target_args src all (n + 1) ys

type alloc_result = (* alloc�ɂ�����spilling�����������ǂ�����\���f�[�^�^ *)
  | Alloc of Id.t (* allocated register *)
  | Spill of Id.t (* spilled variable *)
let rec alloc dest cont regenv x t =
  (* allocate a register or spill a variable *)
  assert (not (Map.containsKey x regenv));
  let all =
    match t with
    | Type.Unit -> ["%r0"] (* dummy *)
    | Type.Float -> allfregs
    | _ -> allregs in
  if all = ["%r0"] then Alloc("%r0") else (* [XX] ad hoc optimization *)
  if is_reg x then Alloc(x) else
  let free = fv_asm cont in
  try
    let (c, prefer) = target x dest cont in
    let live = (* �����Ă��郌�W�X�^ *)
      List.fold
        (fun live y ->
	  if is_reg y then Set.add y live else
          try Set.add (Map.find y regenv) live
          with | :? System.Collections.Generic.KeyNotFoundException -> live)
        Set.empty
        free in
    let r = (* �����łȂ����W�X�^��T�� *)
      List.find
        (fun r -> not (Set.contains r live))
        (prefer @ all) in
    (* Printf.eprintf "allocated %s to %s\n" x r; *)
    Alloc(r)
  with | :? System.Collections.Generic.KeyNotFoundException ->
    Printf.eprintf "register allocation failed for %s\n" x;
    let y = (* �^�̍������W�X�^�ϐ���T�� *)
      List.find
        (fun y ->
	  not (is_reg y) &&
          try List.mem (Map.find y regenv) all
          with | :? System.Collections.Generic.KeyNotFoundException -> false)
        (List.rev free) in
    Printf.eprintf "spilling %s from %s\n" y (Map.find y regenv);
    Spill(y)

(* auxiliary function for g and g'_and_restore *)
let add x r regenv =
  if is_reg x then (assert (x = r); regenv) else
  Map.add x r regenv

(* auxiliary functions for g' *)
exception NoReg of Id.t * Type.t
let find x t regenv =
  if is_reg x then x else
  try Map.find x regenv
  with | :? System.Collections.Generic.KeyNotFoundException -> raise (NoReg(x, t))
let find' x' regenv =
  match x' with
  | V(x) -> V(find x Type.Int regenv)
  | c -> c

let rec g dest cont regenv = function (* ���ߗ�̃��W�X�^���蓖�� (caml2html: regalloc_g) *)
  | Ans(exp) -> g'_and_restore dest cont regenv exp
  | Let((x, t) as xt, exp, e) ->
      assert (not (Map.containsKey x regenv));
      let cont' = concat e dest cont in
      let (e1', regenv1) = g'_and_restore xt cont' regenv exp in
      (match alloc dest cont' regenv1 x t with
      | Spill(y) ->
	  let r = Map.find y regenv1 in
	  let (e2', regenv2) = g dest cont (add x r (Map.remove y regenv1)) e in
	  let save =
	    try Save(Map.find y regenv, y)
	    with | :? System.Collections.Generic.KeyNotFoundException -> Nop in	    
	  (seq(save, concat e1' (r, t) e2'), regenv2)
      | Alloc(r) ->
	  let (e2', regenv2) = g dest cont (add x r regenv1) e in
	  (concat e1' (r, t) e2', regenv2))
and g'_and_restore dest cont regenv exp = (* �g�p�����ϐ����X�^�b�N���烌�W�X�^��Restore (caml2html: regalloc_unspill) *)
  try g' dest cont regenv exp
  with NoReg(x, t) ->
    ((* Printf.eprintf "restoring %s\n" x; *)
     g dest cont regenv (Let((x, t), Restore(x), Ans(exp))))
and g' dest cont regenv = function (* �e���߂̃��W�X�^���蓖�� (caml2html: regalloc_gprime) *)
  | Nop | Li _ | SetL _ | Comment _ | Restore _ | FLi _ as exp -> (Ans(exp), regenv)
  | Mr(x) -> (Ans(Mr(find x Type.Int regenv)), regenv)
  | Neg(x) -> (Ans(Neg(find x Type.Int regenv)), regenv)
  | Add(x, y') -> (Ans(Add(find x Type.Int regenv, find' y' regenv)), regenv)
  | Sub(x, y') -> (Ans(Sub(find x Type.Int regenv, find' y' regenv)), regenv)
  | Slw(x, y') -> (Ans(Slw(find x Type.Int regenv, find' y' regenv)), regenv)
  | Lwz(x, y') -> (Ans(Lwz(find x Type.Int regenv, find' y' regenv)), regenv)
  | Stw(x, y, z') -> (Ans(Stw(find x Type.Int regenv, find y Type.Int regenv, find' z' regenv)), regenv)
  | FMr(x) -> (Ans(FMr(find x Type.Float regenv)), regenv)
  | FNeg(x) -> (Ans(FNeg(find x Type.Float regenv)), regenv)
  | FAdd(x, y) -> (Ans(FAdd(find x Type.Float regenv, find y Type.Float regenv)), regenv)
  | FSub(x, y) -> (Ans(FSub(find x Type.Float regenv, find y Type.Float regenv)), regenv)
  | FMul(x, y) -> (Ans(FMul(find x Type.Float regenv, find y Type.Float regenv)), regenv)
  | FDiv(x, y) -> (Ans(FDiv(find x Type.Float regenv, find y Type.Float regenv)), regenv)
  | Lfd(x, y') -> (Ans(Lfd(find x Type.Int regenv, find' y' regenv)), regenv)
  | Stfd(x, y, z') -> (Ans(Stfd(find x Type.Float regenv, find y Type.Int regenv, find' z' regenv)), regenv)
  | IfEq(x, y', e1, e2) as exp -> g'_if dest cont regenv exp (fun e1' e2' -> IfEq(find x Type.Int regenv, find' y' regenv, e1', e2')) e1 e2
  | IfLE(x, y', e1, e2) as exp -> g'_if dest cont regenv exp (fun e1' e2' -> IfLE(find x Type.Int regenv, find' y' regenv, e1', e2')) e1 e2
  | IfGE(x, y', e1, e2) as exp -> g'_if dest cont regenv exp (fun e1' e2' -> IfGE(find x Type.Int regenv, find' y' regenv, e1', e2')) e1 e2
  | IfFEq(x, y, e1, e2) as exp -> g'_if dest cont regenv exp (fun e1' e2' -> IfFEq(find x Type.Float regenv, find y Type.Float regenv, e1', e2')) e1 e2
  | IfFLE(x, y, e1, e2) as exp -> g'_if dest cont regenv exp (fun e1' e2' -> IfFLE(find x Type.Float regenv, find y Type.Float regenv, e1', e2')) e1 e2
  | CallCls(x, ys, zs) as exp -> g'_call dest cont regenv exp (fun ys zs -> CallCls(find x Type.Int regenv, ys, zs)) ys zs
  | CallDir(l, ys, zs) as exp -> g'_call dest cont regenv exp (fun ys zs -> CallDir(l, ys, zs)) ys zs
  | Save(x, y) -> failwith "regAlloc.fs id:1"
	(*�ǉ�*)
	| Print(x) -> (Ans(Print(find x Type.Int regenv)), regenv)
	| PrintShort(x) -> (Ans(PrintShort(find x Type.Int regenv)), regenv)
	| Scan(x) -> (Ans(Scan(find x Type.Int regenv)), regenv)
	| Sqrt(x) -> (Ans(Sqrt(find x Type.Float regenv)), regenv)
  | Mul(x, y') -> (Ans(Mul(find x Type.Int regenv, find' y' regenv)), regenv)
  | Div(x, y') -> (Ans(Div(find x Type.Int regenv, find' y' regenv)), regenv)
and g'_if dest cont regenv exp constr e1 e2 = (* if�̃��W�X�^���蓖�� (caml2html: regalloc_if) *)
  let (e1', regenv1) = g dest cont regenv e1 in
  let (e2', regenv2) = g dest cont regenv e2 in
  let regenv' = (* �����ɋ��ʂ̃��W�X�^�ϐ��������p *)
    List.fold
      (fun regenv' x ->
        try
	  if is_reg x then regenv' else
          let r1 = Map.find x regenv1 in
          let r2 = Map.find x regenv2 in
          if r1 <> r2 then regenv' else
	  Map.add x r1 regenv'
        with | :? System.Collections.Generic.KeyNotFoundException -> regenv')
      Map.empty
      (fv_asm cont) in
  (List.fold
     (fun e x ->
       if x = fst dest || not (Map.containsKey x regenv) || Map.containsKey x regenv' then e else
       seq(Save(Map.find x regenv, x), e)) (* �����łȂ��ϐ��͕��򒼑O�ɃZ�[�u *)
     (Ans(constr e1' e2'))
     (fv_asm cont),
   regenv')
and g'_call dest cont regenv exp constr ys zs = (* �֐��Ăяo���̃��W�X�^���蓖�� (caml2html: regalloc_call) *)
  (List.fold
     (fun e x ->
       if x = fst dest || not (Map.containsKey x regenv) then e else
       seq(Save(Map.find x regenv, x), e))
     (Ans(constr
	    (List.map (fun y -> find y Type.Int regenv) ys)
	    (List.map (fun z -> find z Type.Float regenv) zs)))
     (fv_asm cont),
   Map.empty)

let h { name = Id.L(x); args = ys; fargs = zs; body = e; ret = t } = (* �֐��̃��W�X�^���蓖�� (caml2html: regalloc_h) *)
  let regenv = Map.add x reg_cl Map.empty in
  let (i, arg_regs, regenv) =
    List.fold
      (fun (i, arg_regs, regenv) y ->
        let r = regs.(i) in
        (i + 1,
	 arg_regs @ [r],
	 (assert (not (is_reg y));
	  Map.add y r regenv)))
      (0, [], regenv)
      ys in
  let (d, farg_regs, regenv) =
    List.fold
      (fun (d, farg_regs, regenv) z ->
        let fr = fregs.(d) in
        (d + 1,
	 farg_regs @ [fr],
	 (assert (not (is_reg z));
	  Map.add z fr regenv)))
      (0, [], regenv)
      zs in
  let a =
    match t with
    | Type.Unit -> Id.gentmp Type.Unit
    | Type.Float -> fregs.(0)
    | _ -> regs.(0) in
  let (e', regenv') = g (a, t) (Ans(Mr(a))) regenv e in
  { name = Id.L(x); args = arg_regs; fargs = farg_regs; body = e'; ret = t }

let f (Prog(data, fundefs, e)) = (* �v���O�����S�̂̃��W�X�^���蓖�� (caml2html: regalloc_f) *)
  Printf.eprintf "register allocation: may take some time (up to a few minutes, depending on the size of functions)\n";
  let fundefs' = List.map h fundefs in
  let e', regenv' = g (Id.gentmp Type.Unit, Type.Unit) (Ans(Nop)) Map.empty e in
  Prog(data, fundefs', e')
