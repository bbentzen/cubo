(**
 * Internal core syntax using de Bruijn indices for local variables.
 * Binder names are preserved as formatting hints.
 **)

type level =
  | Num of int
  | Var of string
  | Suc of level
  | Max of level * level

type var = {
  hint : string;
  index : int;
}

type expr =
  | Local of var
  | Global of string
  | Int of unit
  | I1 of unit
  | I0 of unit
  | Coe of expr * expr * expr * expr
  | Hfill of expr * expr * expr
  | Abs of string * expr
  | App of expr * expr
  | Pi of string * expr * expr
  | Pair of expr * expr
  | Fst of expr
  | Snd of expr
  | Sigma of string * expr * expr
  | Inl of expr
  | Inr of expr
  | Case of expr * expr * expr
  | Sum of expr * expr
  | Star of unit
  | Let of expr * expr
  | Unit of unit
  | True of unit
  | False of unit
  | If of expr * expr * expr
  | Bool of unit
  | Zero of unit
  | Succ of expr
  | Natrec of expr * expr * expr
  | Nat of unit
  | Abort of expr
  | Void of unit
  | Pabs of string * expr
  | At of expr * expr
  | Pathd of expr * expr * expr
  | Type of level
  | Hole of string * (expr list)
  | Wild of int

type proof =
  | Prf of string * (((string list * expr) * bool) list) * expr * expr
