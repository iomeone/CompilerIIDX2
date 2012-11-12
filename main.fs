#indent "off"
module Main
open Elim
open Id
open Printtree

let limit = ref 1000

let rec iter n e = (* 最適化処理をくりかえす (caml2html: main_iter) *)
  Printf.eprintf "iteration %d\n" n;
  if n = 0 then e else
  let e' = Elim.f (ConstFold.f (Inline.f (Assoc.f (Beta.f (Cselim.f e))))) in
  if e = e' then e else
  iter (n - 1) e'

let lexbuf outchan l = (* バッファをコンパイルしてチャンネルへ出力する (caml2html: main_lexbuf) *)
  Id.counter := 0;
  Typing.extenv := Map.empty;
  Emit.f outchan
	(let asmprog = 
		(RegAlloc.f
			(Simm.f
				(Virtual.f
					(let cls = 
						(Closure.f
							(let it = 
								(iter !limit
//							(let cs = 
//								(Cselim.f
									(let al =
										(Alpha.f
											(let kn = 
												(KNormal.f
													(let s = (Typing.f 
														(let le = (Parser.exp Lexer.token l) in le)) in 
														print_string "<Syntax Tree>\n";print_syntax s ();print_string "\n"; s)) in
											print_string "<KNormal Tree>\n";print_knormal kn ();print_string "\n"; kn)) in
									print_string "<KNormal Tree(Alpha-Converted)>\n"; print_knormal al (); print_string "\n"; al)) in
//									print_string "<KNormal Tree(CSeliminated)>\n"; print_knormal cs (); print_string "\n"; cs)) in
							print_string "<KNormal Tree(Optimized)>\n"; print_knormal it (); print_string "\n"; it)) in
					print_string "<Closured Tree>\n"; print_closure cls (); print_string "\n"; cls
					)
				)
			)
		) in
	print_string "<Assembly Tree>\n"; print_assembly asmprog (); print_string "\n"; asmprog
	)

let string s = lexbuf stdout (Lexing.from_string s) (* 文字列をコンパイルして標準出力に表示する (caml2html: main_string) *)

let file f = (* ファイルをコンパイルしてファイルに出力する (caml2html: main_file) *)
  let inchan = open_in (f ^ ".ml") in
  let outchan = open_out (f ^ ".s") in
  try
    lexbuf outchan (Lexing.from_channel inchan);
    close_in inchan;
    close_out outchan;
  with e -> (close_in inchan; close_out outchan; raise e)

let () = (* ここからコンパイラの実行が開始される (caml2html: main_entry) *)
  let files = ref [] in
  Arg.parse
    [("-inline", Arg.Int(fun i -> Inline.threshold := i), "maximum size of functions inlined");
     ("-iter", Arg.Int(fun i -> limit := i), "maximum number of optimizations iterated")]
    (fun s -> files := !files @ [s])
    ("Mitou Min-Caml Compiler (C) Eijiro Sumii\n" ^
     Printf.sprintf "usage: %s [-inline m] [-iter n] ...filenames without \".ml\"..." Sys.argv.(0));
  List.iter
    (fun f -> ignore (file f))
    !files
