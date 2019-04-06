open List;
type formula =
  | Var(string)
  | Not(formula)
  | And(formula, formula)
  | Or(formula, formula)
  | Implication(formula, formula);
type sequent = {
  left: list(formula),
  right: list(formula),
};

let seqToString = (seq: sequent) => {
  let rec helper = formula => {
    switch (formula) {
    | Var(x) => x
    | Not(x) => "!" ++ helper(x)
    | And(x, y) => "(" ++ helper(x) ++ " && " ++ helper(y) ++ ")"
    | Or(x, y) => "(" ++ helper(x) ++ " || " ++ helper(y) ++ ")"
    | Implication(x, y) => "(" ++ helper(x) ++ " => " ++ helper(y) ++ ")"
    };
  };
  fold_left((acc, el) => acc ++ helper(el) ++ ", ", "", seq.left)
  ++ "-> "
  ++ fold_left((acc, el) => acc ++ helper(el) ++ ", ", "", seq.right);
};

let seqsToString = (list: list(sequent)) => {
  map(seqToString, list);
};

let straightChecker = (seq: sequent) => {
  let straightLeftChecker = a =>
    switch (a) {
    | Not(_)
    | And(_, _) => true
    | _ => false
    };
  let straihtRightChecker = a =>
    switch (a) {
    | Not(_)
    | Or(_, _)
    | Implication(_, _) => true
    | _ => false
    };
  exists(straightLeftChecker, seq.left)
  || exists(straihtRightChecker, seq.right);
};

let complicatedChecker = (seq: sequent) => {
  let complicatedLeftChecker = (f: formula) =>
    switch (f) {
    | Or(_, _) => true
    | Implication(_, _) => true
    | _ => false
    };

  let complicatedRightChecker = (f: formula) =>
    switch (f) {
    | And(_, _) => true
    | _ => false
    };

  exists(complicatedLeftChecker, seq.left)
  || exists(complicatedRightChecker, seq.right);
};

let rec straightProcessor = (seq: sequent) => {
  let straigthLeftFolder =
      (acc: (list(formula), list(formula)), el: formula) => {
    let (left, toRight) = acc;
    switch (el) {
    | Not(z) => (left, append(toRight, [z]))
    | And(a, b) => (append(left, [a, b]), toRight)
    | v => (append(left, [v]), toRight)
    };
  };
  let straightRightFolder =
      (acc: (list(formula), list(formula)), el: formula) => {
    let (toLeft, right) = acc;
    switch (el) {
    | Not(v) => (append(toLeft, [v]), right)
    | Or(a, b) => (toLeft, append(right, [a, b]))
    | Implication(a, b) => (append(toLeft, [a]), append(right, [b]))
    | v => (toLeft, append(right, [v]))
    };
  };

  let (l, toRight) = fold_left(straigthLeftFolder, ([], []), seq.left);

  let (toLeft, r) =
    fold_left(straightRightFolder, ([], []), append(seq.right, toRight));

  let res = {left: append(toLeft, l), right: r};

  if (straightChecker(res)) {
    straightProcessor(res);
  } else {
    res;
  };
};

let complicatedProcessor = (seq: sequent) => {
  let rec rightIterator = (prev, curr, l) => {
    switch (curr) {
    | [] => [{left: l, right: prev}]
    | [el, ...tail] =>
      switch (el) {
      | And(a, b) => [
          {left: l, right: append(prev, [a, ...tail])},
          {left: l, right: append(prev, [b, ...tail])},
        ]
      | _ => rightIterator(append(prev, [el]), tail, l)
      }
    };
  };

  let rec leftIterator = (prev, curr, r) => {
    switch (curr) {
    | [] => rightIterator([], r, prev)
    | [el, ...tail] =>
      switch (el) {
      | Or(a, b) => [
          {left: append(prev, [a, ...tail]), right: r},
          {left: append(prev, [b, ...tail]), right: r},
        ]
      | Implication(a, b) => [
          {left: append(prev, [b, ...tail]), right: r},
          {left: append(prev, tail), right: append(r, [a])},
        ]
      | _ => leftIterator(append(prev, [el]), tail, r)
      }
    };
  };
  leftIterator([], seq.left, seq.right);
};

let rec mainProcessor = (seq: sequent) => {
  let s1 = straightProcessor(seq);
  if (complicatedChecker(s1)) {
    let s2 = complicatedProcessor(s1);
    flatten(map(mainProcessor, s2));
  } else {
    [s1];
  };
};

let step = (seq: sequent) => {
  let s1 = straightProcessor(seq);
  if (complicatedChecker(s1)) {
    complicatedProcessor(s1);
  } else {
    [s1];
  };
};

let axiomCheck = (seq: sequent) => {
  fold_left((acc, x) => mem(x, seq.right) || acc, false, seq.left);
};

let allRulesTestingSequent = {
  left: [
    Implication(Var("r"), Var("l")),
    Var("x"),
    Not(Var("a")),
    And(Var("c"), Var("d")),
    Or(Var("n"), Var("f")),
  ],
  right: [
    Implication(Var("m"), Var("w")),
    Var("y"),
    Not(Var("b")),
    And(Var("q"), Var("p")),
    Or(Var("z"), Var("t")),
  ],
};

let testFormula =
  Implication(
    Implication(Or(Var("x"), Var("y")), Or(Var("p"), Var("q"))),
    Or(Var("x"), Not(Var("y"))),
  );

let starter = (f: formula) => {
  let printer = res => {
    Js.log("Left:");
    iter(Js.log, res.left);
    Js.log("Right:");
    iter(Js.log, res.right);
    Js.log("^^^^^");
  };

  let badPrinter = res => {
    let seq = find(s => !axiomCheck(s), res);
    let helperPrinter = (num, el) =>
      switch (el) {
      | Var(e) => Js.log3(e, "=", num)
      | v => Js.log2(v, num)
      };
    iter(helperPrinter(1), seq.left);
    iter(helperPrinter(0), seq.right);
    Js.log("Unlisted variables (if any) may possess any value");
  };
  let seq = {left: [], right: [f]};
  let res = mainProcessor(seq);
  fold_left((acc, seq) => axiomCheck(seq) && acc, true, res)
    ? iter(printer, res) : badPrinter(res);
};

let fToSeq = f => {
  {left: [], right: [f]};
};
