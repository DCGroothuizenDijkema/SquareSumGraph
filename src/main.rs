
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

use squaresum::{square_sum_graph,square_sum_graph_append};

fn main()
{
  let args: Vec<String>=std::env::args().collect();
  let mut input: String;
  if args.len()==1
  {
    // get a number from the user
    print!("Enter n: ");
    std::io::stdout().flush();
    input=String::new();
    std::io::stdin().read_line(&mut input)
      .expect("Failed to read line.");
  }
  else { input=args[1].clone(); }
  let n: u32=match input.trim().parse()
  {
    Ok(num) => num,
    Err(_) => std::process::exit(0),
  };
  drop(input);
  

  // produce the graph and find the hamiltonian path, with timing
  let now: std::time::Instant=std::time::Instant::now();
  let gr: graph::Graph<u32>=square_sum_graph(n);
  println!("{}",gr.hamiltonian_path().unwrap_or(graph::Path::new()));
  println!("Elapsed time: {}ms",now.elapsed().as_millis());
  println!("{}",gr);
}
