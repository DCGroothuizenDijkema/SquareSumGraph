
#![allow(non_snake_case)]
#![allow(unused_must_use)]
#![allow(unused_variables)]

use std::vec::Vec;

mod graph;
use graph::Graph;


fn square_sum_graph(n: u32) -> Graph<u32>
{
  let mut gr: Graph<u32>=Graph::<u32>::new();

  let max: u32=((2*n-1) as f64).sqrt().floor() as u32;
  let pows: Vec<u32>=(2..=max).map(|x| x*x).collect();

  for itr in 1..=n
  {
    gr.add_node(itr).unwrap();
  }

  for itr in 0..gr.order()
  {
    for pow in &pows
    {
      let val: u32=(itr as u32)+1;
      if pow<&val { continue; }

      let diff: u32=pow-val;
      if diff==0 { continue; }

      if diff<=n&&val!=diff { gr.connect(val as u32,diff); }
    }
  }
  
  gr
}


fn main()
{
  let gr: Graph<u32>=square_sum_graph(15);
  println!("{}",gr);
}
