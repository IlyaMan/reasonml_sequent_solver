/*Скипни до следующего коментария, этот блок про графику, тебе не поможет*/

[@bs.deriving abstract]
type node = {
  [@bs.as "id"]
  id: int,
  [@bs.as "label"]
  label: string,
};
[@bs.deriving abstract]
type edge = {
  [@bs.as "from"]
  from: int,
  [@bs.as "to"]
  to_: int,
};
type dataset;
[@bs.module "vis"] [@bs.new]
external createNodes: array(node) => dataset = "DataSet";
[@bs.module "vis"] [@bs.new]
external createEdges: array(edge) => dataset = "DataSet";

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

/*Поехали*/

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

/*Test Formulas*/
let testFormulas = [|
  Implication(
    And(Or(Var("x"), Var("x")), Or(Var("x"), Var("x"))),
    Or(Var("x"), Var("x")),
  ),
  Not(
    Or(
      Implication(And(Var("a"), Var("b")), Or(Var("a"), Var("b"))),
      Not(Var("b")),
    ),
  ),
  And(
    Implication(Or(Var("x"), Var("y")), And(Var("x"), Var("y"))),
    And(Implication(Var("x"), Var("y")), Or(Var("x"), Var("y"))),
  ),
|];

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
    | Implication(x, y) => "(" ++ helper(x) ++ " -> " ++ helper(y) ++ ")"
    };
  };

  let left = join(", ", List.map(helper, seq.left));
  let right = join(", ", List.map(helper, seq.right));
  join(" ", [left, "|-", right]);
};

let seqsToString = (list: list(sequent)) => {
  List.map(seqToString, list);
};

/*Проверяю, можно ли развернуть секвенцию простыми преобразованиями (Без ветвления)*/
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
  List.exists(straightLeftChecker, seq.left)
  || List.exists(straihtRightChecker, seq.right);
};
/*Проверяю, можно ли развернуть секвенцию преобразованиями с ветвлением*/
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

  List.exists(complicatedLeftChecker, seq.left)
  || List.exists(complicatedRightChecker, seq.right);
};

/*Simplifies seq by straight rules*/
let rec straightProcessor = (seq: sequent) => {
  let straigthLeftFolder =
      (acc: (list(formula), list(formula)), el: formula) => {
    let (left, toRight) = acc;
    switch (el) {
    | Not(z) => (left, List.append(toRight, [z]))
    | And(a, b) => (List.append(left, [a, b]), toRight)
    | v => (List.append(left, [v]), toRight)
    };
  };
  let straightRightFolder =
      (acc: (list(formula), list(formula)), el: formula) => {
    let (toLeft, right) = acc;
    switch (el) {
    | Not(v) => (List.append(toLeft, [v]), right)
    | Or(a, b) => (toLeft, List.append(right, [a, b]))
    | Implication(a, b) => (
        List.append(toLeft, [a]),
        List.append(right, [b]),
      )
    | v => (toLeft, List.append(right, [v]))
    };
  };

  let (l, toRight) = List.fold_left(straigthLeftFolder, ([], []), seq.left);

  let (toLeft, r) =
    List.fold_left(
      straightRightFolder,
      ([], []),
      List.append(seq.right, toRight),
    );

  let res = {left: List.append(toLeft, l), right: r};

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
          {left: l, right: List.append(prev, [a, ...tail])},
          {left: l, right: List.append(prev, [b, ...tail])},
        ]
      | _ => rightIterator(List.append(prev, [el]), tail, l)
      }
    };
  };

  let rec leftIterator = (prev, curr, r) => {
    switch (curr) {
    | [] => rightIterator([], r, prev)
    | [el, ...tail] =>
      switch (el) {
      | Or(a, b) => [
          {left: List.append(prev, [a, ...tail]), right: r},
          {left: List.append(prev, [b, ...tail]), right: r},
        ]
      | Implication(a, b) => [
          {left: List.append(prev, [b, ...tail]), right: r},
          {left: List.append(prev, tail), right: List.append(r, [a])},
        ]
      | _ => leftIterator(List.append(prev, [el]), tail, r)
      }
    };
  };
  leftIterator([], seq.left, seq.right);
};

/*Это основная функция, именно она отвечает за получение результата*/
/*Recursive combination of processors*/
let rec mainProcessor = (seq: sequent) => {
  let s1 = straightProcessor(seq);
  if (isComplicated(s1)) {
    let s2 = complicatedProcessor(s1);
    List.flatten(List.map(mainProcessor, s2));
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

/*Проверка на наличие одинаковых формул с разных сторон секвенции*/
let axiomCheck = (seq: sequent) => {
  List.fold_left(
    (acc, x) => List.mem(x, seq.right) || acc,
    false,
    seq.left,
  );
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

/*Счетчик тоже для рисования*/
let counter = {
  let c = ref(0);
  () => {
    c := c^ + 1;
    c^;
  };
};

/*Ну ты понял, тут я рисую, основная логика рекурсии как в mainProcessor*/
let rec draw = (seq, nodeId) =>
  if (isStraight(seq) || isComplicated(seq)) {
    let seqs = step(seq);
    let writer = seq => {
      let c1 = counter();
      nodes :=
        Array.append([|node(~id=c1, ~label=seqToString(seq))|], nodes^);
      edges := Array.append([|edge(~from=nodeId, ~to_=c1)|], edges^);
      draw(seq, c1);
    };

    List.iter(writer, seqs);
  };

/*Отсюда начинаю, делаю секвенцию из формулы и запускаю рекурсию*/
let starter = (f: formula) => {
  let badPrinter = res => {
    Js.log("Counterexample:");
    let seq = List.find(s => !axiomCheck(s), res);
    let helperPrinter = (num, el) =>
      switch (el) {
      | Var(e) => Js.log3(e, "=", num)
      | v => Js.log2(v, num)
      };
    List.iter(helperPrinter(1), seq.left);
    List.iter(helperPrinter(0), seq.right);
    Js.log("Unlisted variables (if any) may possess any value");
  };
  let seq = {left: [], right: [f]};
  let res = mainProcessor(seq);
  List.fold_left((acc, seq) => axiomCheck(seq) && acc, true, res)
    ? Js.log("Tautology") : badPrinter(res);
  /*Осторожно, графика*/
  nodes := Array.append([|node(~id=0, ~label=seqToString(seq))|], nodes^);

  draw(fToSeq(f), 0);
};

/*I have three examples*/
starter(testFormulas[2]);

/*Графика*/
let data = {"nodes": createNodes(nodes^), "edges": createEdges(edges^)};

let network = createNetwork(getElementById("mynetwork"), data, options);
