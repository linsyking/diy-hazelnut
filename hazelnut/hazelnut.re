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

let rec typ_action = (t: ztyp, a: action): option(ztyp) => {
  // A.3.1 Type Actions
  switch (t, a) {
  // Type Movement
  | (Cursor(Arrow(t1, t2)), Move(Child(One))) =>
    Some(LArrow(Cursor(t1), t2))
  | (Cursor(Arrow(t1, t2)), Move(Child(Two))) =>
    Some(RArrow(t1, Cursor(t2)))
  | (LArrow(Cursor(t1), t2), Move(Parent)) => Some(Cursor(Arrow(t1, t2)))
  | (RArrow(t1, Cursor(t2)), Move(Parent)) => Some(Cursor(Arrow(t1, t2)))
  // Type Deletion
  | (Cursor(_), Del) => Some(Cursor(Hole))
  // Type Construction
  | (Cursor(t'), Construct(Arrow)) => Some(RArrow(t', Cursor(Hole)))
  | (Cursor(Hole), Construct(Num)) => Some(Cursor(Num))
  // Zipper Cases
  | (LArrow(t1, t2), _) =>
    let* t1' = typ_action(t1, a);
    Some(LArrow(t1', t2));
  | (RArrow(t1, t2), _) =>
    let* t2' = typ_action(t2, a);
    Some(RArrow(t1, t2'));
  | _ => None
  };
};

let rec exp_move = (e: zexp, dir: dir): option(zexp) => {
  // A.3.2 Expression Movement Actions
  switch (e, dir) {
  // Ascription
  | (Cursor(Asc(e, t)), Child(One)) => Some(LAsc(Cursor(e), t))
  | (Cursor(Asc(e, t)), Child(Two)) => Some(RAsc(e, Cursor(t)))
  | (LAsc(Cursor(e), t), Parent) => Some(Cursor(Asc(e, t)))
  | (RAsc(e, Cursor(t)), Parent) => Some(Cursor(Asc(e, t)))
  // Lambda
  | (Cursor(Lam(x, e)), Child(One)) => Some(Lam(x, Cursor(e)))
  | (Lam(x, Cursor(e)), Parent) => Some(Cursor(Lam(x, e)))
  // Plus
  | (Cursor(Plus(e1, e2)), Child(One)) => Some(LPlus(Cursor(e1), e2))
  | (Cursor(Plus(e1, e2)), Child(Two)) => Some(RPlus(e1, Cursor(e2)))
  | (LPlus(Cursor(e1), e2), Parent) => Some(Cursor(Plus(e1, e2)))
  | (RPlus(e1, Cursor(e2)), Parent) => Some(Cursor(Plus(e1, e2)))
  // Application
  | (Cursor(Ap(e1, e2)), Child(One)) => Some(LAp(Cursor(e1), e2))
  | (Cursor(Ap(e1, e2)), Child(Two)) => Some(RAp(e1, Cursor(e2)))
  | (LAp(Cursor(e1), e2), Parent) => Some(Cursor(Ap(e1, e2)))
  | (RAp(e1, Cursor(e2)), Parent) => Some(Cursor(Ap(e1, e2)))
  // Non-Empty Hole
  | (Cursor(NEHole(e)), Child(One)) => Some(NEHole(Cursor(e)))
  | (NEHole(Cursor(e)), Parent) => Some(Cursor(NEHole(e)))
  | _ => None
  };
};

let rec syn_action =
        (ctx: typctx, (e: zexp, t: htyp), a: action): option((zexp, htyp)) => {
  // A.3.3 Synthetic and Analytic Expression Actions
  switch (e, a, t) {
  // Movement
  | (_, Move(dir), t) =>
    let* e' = exp_move(e, dir);
    Some((e', t));
  // Deletion
  | (Cursor(_), Del, _) => Some((Cursor(EHole), Hole))
  // Construction
  | (Cursor(e'), Construct(Asc), t) => Some((RAsc(e', Cursor(t)), t))
  | (Cursor(EHole), Construct(Var(name)), Hole) =>
    let* t = TypCtx.find_opt(name, ctx);
    Some((Cursor(Var(name)), t));
  | (Cursor(EHole), Construct(Lam(name)), Hole) =>
    Some((
      RAsc(Lam(name, EHole), LArrow(Cursor(Hole), Hole)),
      Arrow(Hole, Hole),
    ))
  | (Cursor(e'), Construct(Ap), t) =>
    switch (t) {
    | Arrow(_, t2) => Some((RAp(e', Cursor(EHole)), t2))
    | Hole => Some((RAp(e', Cursor(EHole)), Hole))
    | _ =>
      // SACONAPOTW
      Some((RAp(NEHole(e'), Cursor(EHole)), Hole))
    }
  | (Cursor(EHole), Construct(Lit(n)), Hole) =>
    Some((Cursor(Lit(n)), Num))
  | (Cursor(e'), Construct(Plus), t) =>
    if (consistent_types(t, Num)) {
      Some((RPlus(e', Cursor(EHole)), Num));
    } else {
      Some((RPlus(NEHole(e'), Cursor(EHole)), Num));
    }
  | (Cursor(e'), Construct(NEHole), _) => Some((NEHole(Cursor(e')), Hole))
  // Finishing
  | (Cursor(NEHole(e)), Finish, Hole) =>
    let* t = syn(ctx, e);
    Some((Cursor(e), t));
  // Zipper Cases
  | (LAsc(e, t'), _, _) =>
    if (t' == t) {
      let* e' = ana_action(ctx, e, a, t);
      Some((LAsc(e', t'), t));
    } else {
      None;
    }
  | (RAsc(e, t'), _, _) =>
    if (erase_typ(t') == t) {
      let* t'' = typ_action(t', a);
      let et = erase_typ(t'');
      if (ana(ctx, e, et)) {
        Some((RAsc(e, t''), et));
      } else {
        None;
      };
    } else {
      None;
    }
  | (LAp(e1, e2), _, _) =>
    let* t2 = syn(ctx, erase_exp(e1));
    let* (e1', t3) = syn_action(ctx, (e1, t2), a);
    switch (t3) {
    | Arrow(t4, t5) =>
      if (ana(ctx, e2, t4)) {
        Some((LAp(e1', e2), t5));
      } else {
        None;
      }
    | Hole =>
      if (ana(ctx, e2, Hole)) {
        Some((LAp(e1', e2), Hole));
      } else {
        None;
      }
    | _ => None
    };
  | (RAp(e1, e2), _, _) =>
    let* t2 = syn(ctx, e1);
    switch (t2) {
    | Arrow(t3, t4) =>
      let* e2' = ana_action(ctx, e2, a, t3);
      Some((RAp(e1, e2'), t4));
    | Hole =>
      let* e2' = ana_action(ctx, e2, a, Hole);
      Some((RAp(e1, e2'), Hole));
    | _ => None
    };
  | (LPlus(e1, e2), _, Num) =>
    let* e1' = ana_action(ctx, e1, a, Num);
    Some((LPlus(e1', e2), Num: htyp));
  | (RPlus(e1, e2), _, Num) =>
    let* e2' = ana_action(ctx, e2, a, Num);
    Some((RPlus(e1, e2'), Num: htyp));
  | (NEHole(e), _, Hole) =>
    let* t = syn(ctx, erase_exp(e));
    let* (e', _) = syn_action(ctx, (e, t), a);
    Some((NEHole(e'): zexp, Hole));
  | _ => None
  };
}

and ana_action = (ctx: typctx, e: zexp, a: action, t: htyp): option(zexp) => {
  switch (e, a, t) {
  // Movement
  | (_, Move(dir), _) =>
    let* e' = exp_move(e, dir);
    Some(e');
  // Deletion
  | (Cursor(_), Del, _) => Some(Cursor(EHole))
  // Construction
  | (Cursor(e'), Construct(Asc), t) => Some(RAsc(e', Cursor(t)))
  | (Cursor(EHole), Construct(Var(name)), t) =>
    let* t' = TypCtx.find_opt(name, ctx);
    if (consistent_types(t, t')) {
      None;
    } else {
      Some(NEHole(Cursor(Var(name))): zexp);
    };
  | (Cursor(EHole), Construct(Lam(name)), Arrow(_, _)) =>
    Some(Lam(name, Cursor(EHole)): zexp)
  | (Cursor(EHole), Construct(Lam(name)), Hole) =>
    Some(Lam(name, Cursor(EHole)): zexp)
  | (Cursor(EHole), Construct(Lam(name)), _) =>
    Some(
      NEHole(RAsc(Lam(name, EHole), LArrow(Cursor(Hole), Hole))): zexp,
    )
  | (Cursor(EHole), Construct(Lit(n)), _) =>
    if (consistent_types(t, Num)) {
      None;
    } else {
      Some(NEHole(Cursor(Lit(n))): zexp);
    }
  // Finishing
  | (Cursor(NEHole(e)), Finish, t) =>
    if (ana(ctx, e, t)) {
      Some(Cursor(e));
    } else {
      None;
    }
  // Zipper Cases
  | (Lam(x, e), _, Arrow(t1, t2)) =>
    let ctx' = TypCtx.add(x, t1, ctx);
    let* e' = ana_action(ctx', e, a, t2);
    Some(Lam(x, e'): zexp);
  | (Lam(x, e), _, Hole) =>
    let ctx' = TypCtx.add(x, Hole, ctx);
    let* e' = ana_action(ctx', e, a, Hole);
    Some(Lam(x, e'): zexp);
  // Subsumption
  | _ =>
    let* t' = syn(ctx, erase_exp(e));
    let* (e', t'') = syn_action(ctx, (e, t'), a);
    if (consistent_types(t, t'')) {
      Some(e');
    } else {
      None;
    };
  };
};
