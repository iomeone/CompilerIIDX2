#indent "off"
module Asm
(* PowerPC assembly with a few virtual instructions *)

type id_or_imm = V of Id.t | C of int
type t = (* 命令の列 *)
  | Ans of exp
  | Let of (Id.t * Type.t) * exp * t
and exp = (* 一つ一つの命令に対応する式 *)
  | Nop
  | Li of int
  | FLi of int
  | SetL of Id.l
  | Mr of Id.t
  | Neg of Id.t
  | Add of Id.t * id_or_imm
  | Sub of Id.t * id_or_imm
  | Slw of Id.t * id_or_imm
  | Lwz of Id.t * id_or_imm
  | Stw of Id.t * Id.t * id_or_imm
  | FMr of Id.t 
  | FNeg of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | Lfd of Id.t * id_or_imm
  | Stfd of Id.t * Id.t * id_or_imm
  | Comment of string
  (* virtual instructions *)
  | IfEq of Id.t * id_or_imm * t * t
  | IfLE of Id.t * id_or_imm * t * t
  | IfGE of Id.t * id_or_imm * t * t
  | IfFEq of Id.t * Id.t * t * t
  | IfFLE of Id.t * Id.t * t * t
  (* closure address, integer arguments, and float arguments *)
  | CallCls of Id.t * Id.t list * Id.t list
  | CallDir of Id.l * Id.t list * Id.t list
  | Save of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 *)
  | Restore of Id.t (* スタック変数から値を復元 *)
	(*追加*)
	| Print of Id.t
	| PrintShort of Id.t
	| Scan of Id.t
	| Sqrt of Id.t
  | Mul of Id.t * id_or_imm
  | Div of Id.t * id_or_imm
type fundef =
    { name : Id.l; args : Id.t list; fargs : Id.t list; body : t; ret : Type.t }
(* プログラム全体 = 浮動小数点数テーブル + トップレベル関数 + メインの式 *)
type prog = Prog of (Id.l * float) list * fundef list * t

(* shorthand of Let for float *)
(* fletd : Id.t * exp * t -> t *)
let fletd (x, e1, e2) = Let ((x, Type.Float), e1, e2)
(* shorthand of Let for unit *)
(* seq : exp * t -> t *)
let seq (e1, e2) = Let ((Id.gentmp Type.Unit, Type.Unit), e1, e2)

let regs = [| "%r2"; "%r5"; "%r6"; "%r7"; "%r8"; "%r9"; "%r10"; 
  "%r11"; "%r12"; "%r13"; "%r16"; "%r17"; "%r18"; 
  "%r19"; "%r20"; "%r21"; "%r22"; "%r23"; "%r24"; "%r25"; "%r26"; 
  "%r27"; "%r28"; "%r29"; "%r30" |]
(* let regs = Array.init 27 (fun i -> Printf.sprintf "_R_%d" i) *)
let fregs = [| "%f1"; "%f2"; "%f3"; "%f4"; "%f5"; "%f6"; "%f7";
  "%f8"; "%f9"; "%f10"; "%f11"; "%f12"; "%f13"; "%f14"; "%f15"; "%f16";
	"%f17"; "%f18"; "%f19"; "%f20"; "%f21"; "%f22"; "%f23"; "%f24"; "%f25";
	"%f26"; "%f27"; "%f28"; "%f29"; "%f30" |]
(*Array.init 32 (fun i -> Printf.sprintf "%%f%d" i)*)
let allregs = Array.toList regs
let allfregs = Array.toList fregs
let reg_cl = regs.[Array.length regs - 1] (* closure address *)
let reg_sw = regs.[Array.length regs - 2] (* temporary for swap *)
let reg_fsw = fregs.[Array.length fregs - 1] (* temporary for swap *)
let reg_hp = "%r4"
let reg_sp = "r1"
let reg_tmp = "r14"
let reg_tmp2 = "r15"
let reg_lr = "r31"
let reg_ftmp = "f31"

(* is_reg : Id.t -> bool *)
let is_reg (x:string) = x.[0] = '%'

(* remove_and_uniq : Set.t -> Id.t list -> Id.t list *)
let rec remove_and_uniq xs = function 
  | [] -> []
  | x :: ys when Set.contains x xs -> remove_and_uniq xs ys
  | x :: ys -> x :: remove_and_uniq (Set.add x xs) ys

(* free variables in the order of use (for spilling) *)
(* fv_id_or_imm : id_or_imm -> Id.t list *)
let fv_id_or_imm = function V (x) -> [x] | _ -> []
(* fv_exp : Id.t list -> t -> Set.t list *)
let rec fv_exp = function
  | Nop | Li (_) | FLi (_) | SetL (_) | Comment (_) | Restore (_) -> []
  | Mr (x) | Neg (x) | FMr (x) | FNeg (x) | Save (x, _) | Print (x) | PrintShort (x) | Scan (x) | Sqrt (x) -> [x]
  | Add (x, y') | Sub (x, y') | Mul (x,y') | Div (x,y') | Slw (x, y') | Lfd (x, y') | Lwz (x, y') -> 
      x :: fv_id_or_imm y'
  | FAdd (x, y) | FSub (x, y) | FMul (x, y) | FDiv (x, y) ->
      [x; y]
  | Stw (x, y, z') | Stfd (x, y, z') -> x :: y :: fv_id_or_imm z'
  | IfEq (x, y', e1, e2) | IfLE (x, y', e1, e2) | IfGE (x, y', e1, e2) -> 
      x :: fv_id_or_imm y' @ remove_and_uniq Set.empty (fv e1 @ fv e2)
  | IfFEq (x, y, e1, e2) | IfFLE (x, y, e1, e2) ->
      x :: y :: remove_and_uniq Set.empty (fv e1 @ fv e2)
  | CallCls (x, ys, zs) -> x :: ys @ zs
  | CallDir (_, ys, zs) -> ys @ zs
and fv = function 
  | Ans (exp) -> fv_exp exp
  | Let ((x, t), exp, e) ->
      fv_exp exp @ remove_and_uniq (Set.singleton x) (fv e)

(* fv_asm : t -> Id.t list *)
let fv_asm e = remove_and_uniq Set.empty (fv e)

(* concat : t -> Id.t * Type.t -> t -> t *)
let rec concat e1 xt e2 = match e1 with
  | Ans (exp) -> Let (xt, exp, e2)
  | Let (yt, exp, e1') -> Let (yt, exp, concat e1' xt e2)

(* align : int -> int *)
//let align i = if i % 8 = 0 then i else i + 4
