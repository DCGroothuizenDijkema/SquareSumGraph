
//+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+//
//                                                                                                                                       //
// main.rs                                                                                                                               //
//                                                                                                                                       //
// D. C. Groothuizen Dijkema - January, 2020                                                                                             //
//+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+//

// Execution file of the square-sum graph problem solution


#![allow(warnings)]

use std::io::Write;

mod graph;
mod squaresum;

use graph::Graph;
use squaresum::{square_sum_graph,square_sum_graph_append};

fn main()
{
  let args: Vec<String>=std::env::args().collect();
  let mut n:u32;
  if args.len()==1
  {
    // get a number from the user
    print!("Enter n: ");
    std::io::stdout().flush();
    let mut guess=String::new();
    std::io::stdin().read_line(&mut guess)
      .expect("Failed to read line.");
    n=match guess.trim().parse()
    {
      Ok(num) => num,
      Err(_) => std::process::exit(0),
    };
  }
  else
  {
    n=match args[1].trim().parse()
    {
      Ok(num) => num,
      Err(_) => std::process::exit(0),
    };
  }
  

  // produce the graph and find the hamiltonian path, with timing
  let now: std::time::Instant=std::time::Instant::now();
  let gr: Graph<u32>=square_sum_graph(n);
  println!("{}",gr.hamiltonian_path().unwrap_or(graph::Path::new()));
  println!("Elapsed time: {}ms",now.elapsed().as_millis());
  println!("{}",gr);
}
