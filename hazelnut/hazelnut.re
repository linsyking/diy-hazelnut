open Sexplib.Std;
open Monad_lib.Monad; // Uncomment this line to use the maybe monad

let compare_string = String.compare;
let compare_int = Int.compare;

[@deriving (sexp, compare)]
type htyp =
  | Arrow(htyp, htyp)
  | Num
  | Hole;

[@deriving (sexp, compare)]
type hexp =
  | Var(string)
  | Lam(string, hexp)
  | Ap(hexp, hexp)
  | Lit(int)
  | Plus(hexp, hexp)
  | Asc(hexp, htyp)
  | EHole
  | NEHole(hexp);

[@deriving (sexp, compare)]
type ztyp =
  | Cursor(htyp)
  | LArrow(ztyp, htyp)
  | RArrow(htyp, ztyp);

[@deriving (sexp, compare)]
type zexp =
  | Cursor(hexp)
  | Lam(string, zexp)
  | LAp(zexp, hexp)
  | RAp(hexp, zexp)
  | LPlus(zexp, hexp)
  | RPlus(hexp, zexp)
  | LAsc(zexp, htyp)
  | RAsc(hexp, ztyp)
  | NEHole(zexp);

[@deriving (sexp, compare)]
type child =
  | One
  | Two;

[@deriving (sexp, compare)]
type dir =
  | Child(child)
  | Parent;

[@deriving (sexp, compare)]
type shape =
  | Arrow
  | Num
  | Asc
  | Var(string)
  | Lam(string)
  | Ap
  | Lit(int)
  | Plus
  | NEHole;

[@deriving (sexp, compare)]
type action =
  | Move(dir)
  | Construct(shape)
  | Del
  | Finish;

module TypCtx = Map.Make(String);
type typctx = TypCtx.t(htyp);

exception Unimplemented;

let rec consistent_types = (t1: htyp, t2: htyp): bool => {
  // Rule 3a-3d
  switch (t1, t2) {
  | (Hole, _) => true
  | (_, Hole) => true
  | (Arrow(t11, t12), Arrow(t21, t22)) =>
    consistent_types(t11, t21) && consistent_types(t12, t22)
  | _ => t1 == t2
  };
};

let rec erase_exp = (e: zexp): hexp => {
  switch (e) {
  | Cursor(e) => e
  | Lam(x, e) => Lam(x, erase_exp(e))
  | LAp(e1, e2) => Ap(erase_exp(e1), e2)
  | RAp(e1, e2) => Ap(e1, erase_exp(e2))
  | LPlus(e1, e2) => Plus(erase_exp(e1), e2)
  | RPlus(e1, e2) => Plus(e1, erase_exp(e2))
  | LAsc(e, t) => Asc(erase_exp(e), t)
  | RAsc(e, t) => Asc(e, erase_typ(t))
  | NEHole(e) => NEHole(erase_exp(e))
  };
}
and erase_typ = (t: ztyp): htyp => {
  switch (t) {
  | Cursor(t) => t
  | LArrow(t1, t2) => Arrow(erase_typ(t1), t2)
  | RArrow(t1, t2) => Arrow(t1, erase_typ(t2))
  };
};

let rec syn = (ctx: typctx, e: hexp): option(htyp) => {
  switch (e) {
  | Var(x) => TypCtx.find_opt(x, ctx) // Rule 1a
  | Ap(e1, e2) =>
    // Rule 1b
    let* t1 = syn(ctx, e1);
    switch (t1) {
    | Arrow(t11, t12) =>
      if (ana(ctx, e2, t11)) {
        Some(t12);
      } else {
        None;
      }
    | Hole =>
      if (ana(ctx, e2, Hole)) {
        Some(Hole);
      } else {
        None;
      }
    | _ => None
    };
  | Lit(_) => Some(Num) // Rule 1c
  | Plus(e1, e2) =>
    // Rule 1d
    if (ana(ctx, e1, Num) && ana(ctx, e2, Num)) {
      Some(Num);
    } else {
      None;
    }
  | Asc(e, t) =>
    // Rule 1e
    if (ana(ctx, e, t)) {
      Some(t);
    } else {
      None;
    }
  | EHole => Some(Hole) // Rule 1f
  | NEHole(e) =>
    // Rule 1g
    let* _ = syn(ctx, e);
    Some(Hole);
  | Lam(_, _) => None
  };
}

and ana = (ctx: typctx, e: hexp, t: htyp): bool => {
  switch (e) {
  | Lam(x, e) =>
    // Rule 2a
    switch (t) {
    | Arrow(t1, t2) =>
      let ctx' = TypCtx.add(x, t1, ctx);
      ana(ctx', e, t2);
    | Hole =>
      let ctx' = TypCtx.add(x, Hole, ctx);
      ana(ctx', e, Hole);
    | _ => false
    }
  | _ =>
    // Rule 2b
    switch (syn(ctx, e)) {
    | Some(t') => consistent_types(t, t')
    | None => false
    }
  };
};

let syn_action =
    (ctx: typctx, (e: zexp, t: htyp), a: action): option((zexp, htyp)) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = t;
  let _ = a;
  print_endline("syn_action unimplemented");

  Some((e, t));
}

and ana_action = (ctx: typctx, e: zexp, a: action, t: htyp): option(zexp) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = a;
  let _ = t;

  raise(Unimplemented);
};
