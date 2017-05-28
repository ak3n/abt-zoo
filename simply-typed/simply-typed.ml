open Core_kernel.Core_printf
open Operator
open Abt
open List

(* 

  The implementation of simply typed lambda calculus with the following grammar:

    terms            e ::= true | false | e1 e2 | \x:t.e | if e then e else e
    types            t ::= t1 -> t2 | bool
*)

type simply_typed_op =
    True
  | False
  | If
  | Lam
  | Ap
  | Bool
  | Arrow

module SimplyTypedOp : OPERATOR with type t = simply_typed_op = struct
  type t = simply_typed_op

  let arity op =
    match op with
    | True -> []
    | False -> []
    | If -> [0; 0; 0]
    | Lam -> [1]
    | Ap -> [0; 0]
    | Bool -> []
    | Arrow -> [0; 0]

  let equal (x, y) =
    match (x, y) with
    | True, True -> true
    | False, False -> true
    | If, If -> true
    | Lam, Lam -> true
    | Ap, Ap -> true
    | Bool, Bool -> true
    | Arrow, Arrow -> true
    | _ -> false

  let to_string op =
    match op with
      True -> "true"
    | False -> "false"
    | If -> "if"
    | Lam -> "lam"
    | Ap -> "ap"
    | Bool -> "bool"
    | Arrow -> "arrow"
end

module SimplyTypedTerm = MakeAbt(SimplyTypedOp)

open SimplyTypedTerm
open Variable

type ctx = (Variable.t * simply_typed_op) list

exception NotInScope of string
exception NotFunction of simply_typed_op
exception Mismatch of simply_typed_op * simply_typed_op

