open Core_kernel.Core_printf
open Core_kernel.Core_list
open Operator
open Abt

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

