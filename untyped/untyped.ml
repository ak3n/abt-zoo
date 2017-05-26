open Core_kernel.Core_printf
open Operator
open Abt
open List

type untyped_op =
    Lam
  | Ap

module UntypedOp : OPERATOR with type t = untyped_op = struct
  type t = untyped_op

  let arity op =
    match op with
    | Lam -> [1]
    | Ap -> [0; 0]

  let equal (x, y) =
    match (x, y) with
    | Lam, Lam -> true
    | Ap, Ap -> true
    | _ -> false

  let to_string op =
    match op with
    | Lam -> "lam"
    | Ap -> "ap"
end

module UntypedTerm = MakeAbt(UntypedOp)

open UntypedTerm
open Variable

(* call-by-value *)
let rec eval e =
  into (
    match out e with
    (* beta reduction *)
    | AppView (Ap, [a; y]) ->
        (match out a with
        | AppView (Lam, [a]) ->
            (match out a with
            | AbsView (x, e) -> out (eval (subst y x e));
            | x -> x)
        | AppView (_, _) ->
          let eval_a = eval a in
          let eval_y = eval y in
            out (eval (Ap $$ [eval_a; eval_y]))
        | x -> x)
    (* eta conversion *)
    | AppView (Lam, [a]) ->
      (match out a with
      | AbsView (x, e) ->
        (match out e with
        | AppView (Ap, [f; xvar]) ->
            (match out xvar with
            | VarView xx -> 
              if (equal (x, xx)) && not (exists (fun y -> equal (xx, y)) (freevars f)) then
                out f
              else
                AppView (Ap, [f; xvar])
            | x -> x)
        | x -> x)
      | x -> x)
    | x -> x
  )

let _ =
  let x = newvar "x" in
  let y = newvar "y" in

  (* \x.x *)
  let id = Lam $$ [x ^^ !! x] in

  (* ((\x.x) y) *)
  let t = Ap $$ [id; !! y] in
  print_string (UntypedTerm.to_string t ^ "\n");

  let tt = eval t in
  print_string (UntypedTerm.to_string tt ^ "\n");

  let a = newvar "a" in
  let b = newvar "b" in

  (* \a.\b.a *)
  let _true = Lam $$ [a ^^ (Lam $$ [b ^^ !! a])] in
  print_string (UntypedTerm.to_string _true ^ "\n");

  (* \a.\b.b *)
  let _false = Lam $$ [a ^^ (Lam $$ [b ^^ !! b])] in
  print_string (UntypedTerm.to_string _false ^ "\n");

  (* \x.\y.\a.((x y) a *)
  let _if = Lam $$ [x ^^ (Lam $$ [y ^^ (Lam $$ [a ^^ (Ap $$ [(Ap $$ [!! x; !! y]); !! a])])])] in
  print_string (UntypedTerm.to_string _if ^ "\n");

  let if_true_then_true = eval (Ap $$ [(Ap $$ [(Ap $$ [_if; _true]); _true]); _false]) in
  print_string (UntypedTerm.to_string if_true_then_true ^ "\n");    

  (* \a.\b. if a b false *)
  let _and = Lam $$ [a ^^ (Lam $$ [b ^^ (Ap $$ [
                                            (Ap $$ [
                                              (Ap $$ [_if; !! a]
                                              ); !! b]
                                            ); _false]
                                        )
                                  ]
                          )
                    ] in
  print_string (UntypedTerm.to_string _and ^ "\n");

  (* eval (and true false) *)
  let and_true_false = eval (Ap $$ [(Ap $$ [_and; _true]); _false]) in
  print_string (UntypedTerm.to_string and_true_false ^ "\n");

  let f = newvar "f" in
  let y_combinator = Lam $$ [f ^^ (Ap $$ [(Lam $$ [x ^^ (Ap $$ [!! f; (Ap $$ [!! x; !! x])])]);
                                          (Lam $$ [x ^^ (Ap $$ [!! f; (Ap $$ [!! x; !! x])])])])] in
  print_string (UntypedTerm.to_string y_combinator ^ "\n");

  let omega = Ap $$ [(Lam $$ [x ^^ (Ap $$ [!! x; !! x])]);
                     (Lam $$ [x ^^ (Ap $$ [!! x; !! x])])] in
  print_string (UntypedTerm.to_string omega ^ "\n");

  (* Stack overflow *)
  (* eval omega *)

  (* check eta conversion *)
  let term = Lam $$ [x ^^ (Ap $$ [!! f; !! x])] in
  print_string (UntypedTerm.to_string term ^ "\n");
  print_string (UntypedTerm.to_string (eval term) ^ "\n");
