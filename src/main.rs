
#![allow(non_snake_case)]

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
  
  gr
}


fn main()
{
  let gr: Graph<u32>=square_sum_graph(15);
}
