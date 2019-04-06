open Array;
open List;

type node = {
  id: int,
  label: string,
};
type edge = {
  from: int,
  to_: int,
};
type dataset;
[@bs.module "vis"] [@bs.new]
external createDataset: array(node) => dataset = "DataSet";
[@bs.module "vis"] [@bs.new]
external createDataset_: array(edge) => dataset = "DataSet";

let nodes: ref(array(node)) = ref([||]);
let edges: ref(array(edge)) = ref([||]);

let options = {
  "layout": {
    hierarchical: {
      direction: "UD",
      sortMethod: "directed",
      levelSeparation: 100,
      nodeSpacing: 400,
    },
  },
  "interaction": {
    dragNodes: false,
  },
  "physics": {
    enabled: false,
  },
};

type network;
[@bs.module "vis"] [@bs.new]
external createNetwork: ('container_t, 'data_t, 'options_t) => network =
  "Network";

type element;
[@bs.val] [@bs.return nullable] [@bs.scope "document"]
external getElementById: string => option(element) = "getElementById";

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

/* Stolen from SO */
let rec join = (char: string, list: list(string)): string => {
  switch (list) {
  | [] => ""
  | [tail] => tail
  | [head, ...tail] => head ++ char ++ join(char, tail)
  };
};

let fToSeq = f => {
  {left: [], right: [f]};
};
/**/

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

  let left = join(", ", map(helper, seq.left));
  let right = join(", ", map(helper, seq.right));
  join(" ", [left, "->", right]);
};

let seqsToString = (list: list(sequent)) => {
  map(seqToString, list);
};

let isStraight = (seq: sequent) => {
  /*Checks if seq may be simplified by straight rules*/
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

let isComplicated = (seq: sequent) => {
  /*Checks if seq may be simplified by branching rules*/
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

/*Simplifies seq by straight rules*/
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

  if (isStraight(res)) {
    straightProcessor(res);
  } else {
    res;
  };
};

/*Simplifies seq by branching rules*/
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

/*Recursive combination of processors*/
let rec mainProcessor = (seq: sequent) => {
  let s1 = straightProcessor(seq);
  if (isComplicated(s1)) {
    let s2 = complicatedProcessor(s1);
    flatten(map(mainProcessor, s2));
  } else {
    [s1];
  };
};

let step = (seq: sequent) => {
  let s1 = straightProcessor(seq);
  if (isComplicated(s1)) {
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

let c = ref(0);
let count = () => {
  c := c^ + 1;
  c^;
};

let rec jsProcessor = (seq, nodeId) =>
  if (isStraight(seq) || isComplicated(seq)) {
    let seqs = step(seq);
    let formulas = seqsToString(seqs);
    let c1 = count();
    nodes := Array.append([|{id: c1, label: hd(formulas)}|], nodes^);
    edges := Array.append([|{from: nodeId, to_: c1}|], edges^);
    jsProcessor(hd(seqs), c1);

    if (length(seqs) == 2) {
      let c2 = count();
      nodes := Array.append([|{id: c2, label: hd(formulas)}|], nodes^);
      edges := Array.append([|{from: nodeId, to_: c2}|], edges^);
      jsProcessor(hd(tl(seqs)), c2);
    } else {
      Js.log2(seqToString(hd(seqs)), seqToString(hd(tl(seqs))));
    };
  };

/*The Formula*/
let testFormula =
  Implication(
    And(Or(Var("x"), Var("x")), Or(Var("x"), Var("x"))),
    Or(Var("x"), Var("x")),
  );

let starter = (f: formula) => {
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
    ? Js.log("Tautology") : badPrinter(res);
  jsProcessor(fToSeq(f), 0);
};

starter(testFormula);

let data = {
  "nodes": createDataset(nodes^),
  "edges": createDataset_(edges^),
};
Js.log(nodes^);
let network = createNetwork(getElementById("mynetwork"), data, options);

network;
