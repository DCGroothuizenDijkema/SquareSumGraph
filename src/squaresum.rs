
//+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+//
//                                                                                                                                       //
// squaresum.rs                                                                                                                          //
//                                                                                                                                       //
// D. C. Groothuizen Dijkema - January, 2020                                                                                             //
//+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+//

// Functions to create square-sum graphs


use crate::graph::Graph;

/// Produce a square-sum Graph up to a given number.
pub fn square_sum_graph(n: u32) -> Graph<u32>
{
  let mut gr: Graph<u32>=Graph::<u32>::new();

  // determine the powers that the numbers up to n *could* sum to
  let max: u32=((2*n-1) as f64).sqrt().floor() as u32;
  let squares: Vec<u32>=(2..=max).map(|x| x*x).collect();

  // add all nodes
  for itr in 1..=n
  {
    gr.add_node(itr).unwrap();
  }

  // connect all two nodes whose sum is a square
  for itr in 1..=gr.order()
  {
    for sq in &squares
    {
      let val: u32=itr as u32;
      if sq<&val { continue; }

      let diff: u32=sq-val;
      if diff==0 { continue; }

      if diff<=n&&val!=diff { gr.connect(val as u32,diff); }
    }
  }
  
  gr
}

/// Append a Node to a square-sum Graph.
/// 
/// Makes no changes to the Graph if all natural numbers up to n are not already in the Graph, or if the Node is already in the Graph.
pub fn square_sum_graph_append(gr: &mut Graph<u32>, n: u32)
{
  // all natural numbers up to n are in the Graph
  if gr.order()+1!=n as usize { return; }

  // append and return on error
  let res=gr.add_node(n);
  if res.is_err() { return; }

  // determine the maximum power used to create the previous Graph, and that for the number to add
  let prev_max: u32=((2*n-3) as f64).sqrt().floor() as u32;
  let max: u32=((2*n-1) as f64).sqrt().floor() as u32;

  let squares: Vec<u32>=(2..=max).map(|x| x*x).collect();

  // if the maximum has changed, we need to consider Nodes in the Graph adding to the new power
  if prev_max!=max
  {
    // connect previous Nodes which add to the new power, but only the new square
    for itr in 0..gr.order()-1
    {
      let sq: &u32=squares.last().unwrap();
      let val: u32=(itr as u32)+1;
      if sq<&val { continue; }

      let diff: u32=sq-val;
      if diff==0 { continue; }

      if diff<=n&&val!=diff { gr.connect(val as u32,diff); }
    }
  }
  // connect the new Node to all Nodes which make all of the squares
  for sq in squares
  {
    if sq<n { continue; }

    let diff: u32=sq-n;
    if diff==0 { continue; }

    if diff<=n&&n!=diff { gr.connect(n as u32,diff); }
  }
}
