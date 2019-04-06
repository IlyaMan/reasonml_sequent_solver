let vis = require("vis")
let P = require("./Demo.bs")

let c = 0

function count() {
  c += 1
  return c
}
let nodes = []
let edges = []

function jsProcessor(seq, nodeId) {
  if ((seq == undefined) || !P.isStraight(seq) && !P.isComplicated(seq)) {
    return
  }
  let seqs = P.step(seq)
  let formulas = P.seqsToString(seqs)
  if (seqs[0] != undefined) {
    let c1 = count()
    nodes.push({
      id: c1,
      label: formulas[0]
    })
    edges.push({
      from: nodeId,
      to: c1
    })
    jsProcessor(seqs[0], c1)
  }

  if (seqs[1][0] != undefined) {
    let c2 = count()
    nodes.push({
      id: c2,
      label: formulas[1][0]
    })
    edges.push({
      from: nodeId,
      to: c2
    })
    jsProcessor(seqs[1][0], c2)
  }

};

function jsStarter(formula) {
  let seq = P.fToSeq(formula)
  nodes.push({
    id: 0,
    label: P.seqToString(seq)
  })
  jsProcessor(seq, 0)
  P.starter(formula)

}

jsStarter(P.testFormula, 0)
var container = document.getElementById('mynetwork');
var data = {
  nodes: new vis.DataSet(nodes),
  edges: new vis.DataSet(edges)
};
var options = {
  layout: {
    hierarchical: {
      direction: "UD",
      sortMethod: "directed",
      levelSeparation: 100,
      nodeSpacing: 400
    }
  },
  interaction: {
    dragNodes: false
  },
  physics: {
    enabled: false
  }
};
var network = new vis.Network(container, data, options);
