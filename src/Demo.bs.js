// Generated by BUCKLESCRIPT VERSION 4.0.7000, PLEASE EDIT WITH CARE
'use strict';

var List = require("bsb-native/lib/js/list.js");
var Block = require("bsb-native/lib/js/block.js");

function seqToString(seq) {
  var helper = function (formula) {
    switch (formula.tag | 0) {
      case 0 : 
          return formula[0];
      case 1 : 
          return "!" + helper(formula[0]);
      case 2 : 
          return "(" + (helper(formula[0]) + (" && " + (helper(formula[1]) + ")")));
      case 3 : 
          return "(" + (helper(formula[0]) + (" || " + (helper(formula[1]) + ")")));
      case 4 : 
          return "(" + (helper(formula[0]) + (" => " + (helper(formula[1]) + ")")));
      
    }
  };
  return List.fold_left((function (acc, el) {
                return acc + (helper(el) + ", ");
              }), "", seq[/* left */0]) + ("-> " + List.fold_left((function (acc, el) {
                  return acc + (helper(el) + ", ");
                }), "", seq[/* right */1]));
}

function straightChecker(seq) {
  var straightLeftChecker = function (a) {
    switch (a.tag | 0) {
      case 1 : 
      case 2 : 
          return true;
      default:
        return false;
    }
  };
  var straihtRightChecker = function (a) {
    switch (a.tag | 0) {
      case 0 : 
      case 2 : 
          return false;
      default:
        return true;
    }
  };
  if (List.exists(straightLeftChecker, seq[/* left */0])) {
    return true;
  } else {
    return List.exists(straihtRightChecker, seq[/* right */1]);
  }
}

function complicatedChecker(seq) {
  var complicatedLeftChecker = function (f) {
    switch (f.tag | 0) {
      case 3 : 
      case 4 : 
          return true;
      default:
        return false;
    }
  };
  var complicatedRightChecker = function (f) {
    if (f.tag === 2) {
      return true;
    } else {
      return false;
    }
  };
  if (List.exists(complicatedLeftChecker, seq[/* left */0])) {
    return true;
  } else {
    return List.exists(complicatedRightChecker, seq[/* right */1]);
  }
}

function straightProcessor(_seq) {
  while(true) {
    var seq = _seq;
    var straigthLeftFolder = function (acc, el) {
      var toRight = acc[1];
      var left = acc[0];
      switch (el.tag | 0) {
        case 1 : 
            return /* tuple */[
                    left,
                    List.append(toRight, /* :: */[
                          el[0],
                          /* [] */0
                        ])
                  ];
        case 2 : 
            return /* tuple */[
                    List.append(left, /* :: */[
                          el[0],
                          /* :: */[
                            el[1],
                            /* [] */0
                          ]
                        ]),
                    toRight
                  ];
        default:
          return /* tuple */[
                  List.append(left, /* :: */[
                        el,
                        /* [] */0
                      ]),
                  toRight
                ];
      }
    };
    var straightRightFolder = function (acc, el) {
      var right = acc[1];
      var toLeft = acc[0];
      var exit = 0;
      switch (el.tag | 0) {
        case 1 : 
            return /* tuple */[
                    List.append(toLeft, /* :: */[
                          el[0],
                          /* [] */0
                        ]),
                    right
                  ];
        case 0 : 
        case 2 : 
            exit = 1;
            break;
        case 3 : 
            return /* tuple */[
                    toLeft,
                    List.append(right, /* :: */[
                          el[0],
                          /* :: */[
                            el[1],
                            /* [] */0
                          ]
                        ])
                  ];
        case 4 : 
            return /* tuple */[
                    List.append(toLeft, /* :: */[
                          el[0],
                          /* [] */0
                        ]),
                    List.append(right, /* :: */[
                          el[1],
                          /* [] */0
                        ])
                  ];
        
      }
      if (exit === 1) {
        return /* tuple */[
                toLeft,
                List.append(right, /* :: */[
                      el,
                      /* [] */0
                    ])
              ];
      }
      
    };
    var match = List.fold_left(straigthLeftFolder, /* tuple */[
          /* [] */0,
          /* [] */0
        ], seq[/* left */0]);
    var match$1 = List.fold_left(straightRightFolder, /* tuple */[
          /* [] */0,
          /* [] */0
        ], List.append(seq[/* right */1], match[1]));
    var res_000 = /* left */List.append(match$1[0], match[0]);
    var res_001 = /* right */match$1[1];
    var res = /* record */[
      res_000,
      res_001
    ];
    if (straightChecker(res)) {
      _seq = res;
      continue ;
    } else {
      return res;
    }
  };
}

function complicatedProcessor(seq) {
  var _prev = /* [] */0;
  var _curr = seq[/* left */0];
  var r = seq[/* right */1];
  while(true) {
    var curr = _curr;
    var prev = _prev;
    if (curr) {
      var tail = curr[1];
      var el = curr[0];
      switch (el.tag | 0) {
        case 3 : 
            return /* :: */[
                    /* record */[
                      /* left */List.append(prev, /* :: */[
                            el[0],
                            tail
                          ]),
                      /* right */r
                    ],
                    /* :: */[
                      /* record */[
                        /* left */List.append(prev, /* :: */[
                              el[1],
                              tail
                            ]),
                        /* right */r
                      ],
                      /* [] */0
                    ]
                  ];
        case 4 : 
            return /* :: */[
                    /* record */[
                      /* left */List.append(prev, /* :: */[
                            el[1],
                            tail
                          ]),
                      /* right */r
                    ],
                    /* :: */[
                      /* record */[
                        /* left */List.append(prev, tail),
                        /* right */List.append(r, /* :: */[
                              el[0],
                              /* [] */0
                            ])
                      ],
                      /* [] */0
                    ]
                  ];
        default:
          _curr = tail;
          _prev = List.append(prev, /* :: */[
                el,
                /* [] */0
              ]);
          continue ;
      }
    } else {
      var _prev$1 = /* [] */0;
      var _curr$1 = r;
      var l = prev;
      while(true) {
        var curr$1 = _curr$1;
        var prev$1 = _prev$1;
        if (curr$1) {
          var tail$1 = curr$1[1];
          var el$1 = curr$1[0];
          if (el$1.tag === 2) {
            return /* :: */[
                    /* record */[
                      /* left */l,
                      /* right */List.append(prev$1, /* :: */[
                            el$1[0],
                            tail$1
                          ])
                    ],
                    /* :: */[
                      /* record */[
                        /* left */l,
                        /* right */List.append(prev$1, /* :: */[
                              el$1[1],
                              tail$1
                            ])
                      ],
                      /* [] */0
                    ]
                  ];
          } else {
            _curr$1 = tail$1;
            _prev$1 = List.append(prev$1, /* :: */[
                  el$1,
                  /* [] */0
                ]);
            continue ;
          }
        } else {
          return /* :: */[
                  /* record */[
                    /* left */l,
                    /* right */prev$1
                  ],
                  /* [] */0
                ];
        }
      };
    }
  };
}

function mainProcessor(seq) {
  var s1 = straightProcessor(seq);
  if (complicatedChecker(s1)) {
    var s2 = complicatedProcessor(s1);
    return List.flatten(List.map(mainProcessor, s2));
  } else {
    return /* :: */[
            s1,
            /* [] */0
          ];
  }
}

function axiomCheck(seq) {
  return List.fold_left((function (acc, x) {
                if (List.mem(x, seq[/* right */1])) {
                  return true;
                } else {
                  return acc;
                }
              }), false, seq[/* left */0]);
}

var allRulesTestingSequent = /* record */[
  /* left : :: */[
    /* Implication */Block.__(4, [
        /* Var */Block.__(0, ["r"]),
        /* Var */Block.__(0, ["l"])
      ]),
    /* :: */[
      /* Var */Block.__(0, ["x"]),
      /* :: */[
        /* Not */Block.__(1, [/* Var */Block.__(0, ["a"])]),
        /* :: */[
          /* And */Block.__(2, [
              /* Var */Block.__(0, ["c"]),
              /* Var */Block.__(0, ["d"])
            ]),
          /* :: */[
            /* Or */Block.__(3, [
                /* Var */Block.__(0, ["n"]),
                /* Var */Block.__(0, ["f"])
              ]),
            /* [] */0
          ]
        ]
      ]
    ]
  ],
  /* right : :: */[
    /* Implication */Block.__(4, [
        /* Var */Block.__(0, ["m"]),
        /* Var */Block.__(0, ["w"])
      ]),
    /* :: */[
      /* Var */Block.__(0, ["y"]),
      /* :: */[
        /* Not */Block.__(1, [/* Var */Block.__(0, ["b"])]),
        /* :: */[
          /* And */Block.__(2, [
              /* Var */Block.__(0, ["q"]),
              /* Var */Block.__(0, ["p"])
            ]),
          /* :: */[
            /* Or */Block.__(3, [
                /* Var */Block.__(0, ["z"]),
                /* Var */Block.__(0, ["t"])
              ]),
            /* [] */0
          ]
        ]
      ]
    ]
  ]
];

function starter(f) {
  var printer = function (res) {
    console.log("Left:");
    List.iter((function (prim) {
            console.log(prim);
            return /* () */0;
          }), res[/* left */0]);
    console.log("Right:");
    List.iter((function (prim) {
            console.log(prim);
            return /* () */0;
          }), res[/* right */1]);
    console.log("^^^^^");
    return /* () */0;
  };
  var seq_001 = /* right : :: */[
    f,
    /* [] */0
  ];
  var seq = /* record */[
    /* left : [] */0,
    seq_001
  ];
  var res = mainProcessor(seq);
  var match = List.fold_left((function (acc, seq) {
          if (axiomCheck(seq)) {
            return acc;
          } else {
            return false;
          }
        }), true, res);
  if (match) {
    return List.iter(printer, res);
  } else {
    var res$1 = res;
    var seq$1 = List.find((function (s) {
            return !axiomCheck(s);
          }), res$1);
    var helperPrinter = function (num, el) {
      if (el.tag) {
        console.log(el, num);
        return /* () */0;
      } else {
        console.log(el[0], "=", num);
        return /* () */0;
      }
    };
    List.iter((function (param) {
            return helperPrinter(1, param);
          }), seq$1[/* left */0]);
    List.iter((function (param) {
            return helperPrinter(0, param);
          }), seq$1[/* right */1]);
    console.log("Unlisted variables (if any) may possess any value");
    return /* () */0;
  }
}

seqToString(allRulesTestingSequent);

var testFormula = /* Implication */Block.__(4, [
    /* Implication */Block.__(4, [
        /* Or */Block.__(3, [
            /* Var */Block.__(0, ["x"]),
            /* Var */Block.__(0, ["y"])
          ]),
        /* Or */Block.__(3, [
            /* Var */Block.__(0, ["p"]),
            /* Var */Block.__(0, ["q"])
          ])
      ]),
    /* Or */Block.__(3, [
        /* Var */Block.__(0, ["x"]),
        /* Not */Block.__(1, [/* Var */Block.__(0, ["y"])])
      ])
  ]);

exports.seqToString = seqToString;
exports.straightChecker = straightChecker;
exports.complicatedChecker = complicatedChecker;
exports.straightProcessor = straightProcessor;
exports.complicatedProcessor = complicatedProcessor;
exports.mainProcessor = mainProcessor;
exports.axiomCheck = axiomCheck;
exports.allRulesTestingSequent = allRulesTestingSequent;
exports.testFormula = testFormula;
exports.starter = starter;
/*  Not a pure module */
