
//+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+//
//                                                                                                                                       //
// graph.rs                                                                                                                              //
//                                                                                                                                       //
// D. C. Groothuizen Dijkema - January, 2020                                                                                             //
//+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+//

// Graph theory related classes, traits, and impls


#![allow(dead_code)]
#![allow(unused_variables)]

use std::cell::RefCell;
use std::rc::Rc;
use std::vec::Vec;
use std::option::Option;
use std::result::Result;
use std::collections::VecDeque;


//
// Traits
//

pub trait Scalar:
  std::cmp::PartialEq
  + std::marker::Copy
  + std::fmt::Display
{
}
  
  impl<T> Scalar for T where T:
  std::cmp::PartialEq
  + std::marker::Copy
  + std::fmt::Display
{
}


//
// Structs
//

pub struct Node<T>
  where T: Scalar
{
  val: T,
  edges: Vec<Rc<RefCell<Edge<T>>>>,
}

impl<T> Node<T>
  where T: Scalar
{
  /// Returns a new Node with a given value and an empty Vec of Edges.
  pub fn new(val: T) -> Self
  {
    Node{val:val,edges:Vec::<Rc<RefCell<Edge<T>>>>::new()}
  }

  /// Returns the value of a Node
  pub fn val(&self) -> T
  {
    self.val
  }

  /// Return a Vec of all Nodes adjacent to a Node
  pub fn adjacent_nodes(&self) -> Option<Vec<Rc<RefCell<Node<T>>>>>
  {
    if !self.is_isolated()
    {
      let mut adj_nds: Vec<Rc<RefCell<Node<T>>>>=Vec::<Rc<RefCell<Node<T>>>>::new();
      for edge in &self.edges
      {
        for connected_nd in &edge.borrow().nodes
        {
          let connected_val: T=connected_nd.borrow().val();
          // we may have found the current Node so continue
          if connected_val==self.val { continue; }
          adj_nds.push(Rc::clone(&connected_nd));
        }
      }
      return Option::Some(adj_nds);
    }
    Option::None
  }

  /// Returns the number of Edges connected to a Node
  pub fn degree(&self) -> usize
  {
    self.edges.len()
  }

  /// Returns true if no Edges are connectd to a Node, false otherwise
  pub fn is_isolated(&self) -> bool
  {
    self.degree()==0
  }

  /// Returns true if only one Edge is connected to a Node, false otherwise
  pub fn is_leaf(&self) -> bool
  {
    self.degree()==1
  }
}

impl<T> std::cmp::PartialEq for Node<T>
  where T: Scalar
{
  fn eq(&self, other: &Self) -> bool
  {
    // Nodes are equal if there values are equal
    self.val==other.val
  }
}

impl<T> std::cmp::Eq for Node<T>
  where T: Scalar
{
}

impl<T> std::fmt::Display for Node<T>
  where T: Scalar
{
  fn fmt(&self,f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
  {
    write!(f,"{}",self.val)
  }
}

pub struct Edge<T>
  where T: Scalar
{
  nodes: Vec<Rc<RefCell<Node<T>>>>,
}

impl<T> std::fmt::Display for Edge<T>
  where T: Scalar
{
  fn fmt(&self,f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
  {
    write!(f,"{} - {}",self.nodes[0].borrow(),self.nodes[1].borrow())
  }
}

pub struct Graph<T>
  where T: Scalar
{
  nodes: Vec<Rc<RefCell<Node<T>>>>,
  edges: Vec<Rc<RefCell<Edge<T>>>>,
}

impl<T> Graph<T>
  where T: Scalar
{
  /// Returns a new Graph with an empty Vec of Nodes and Edges.
  pub fn new() -> Self
  {
    Graph{nodes:Vec::<Rc<RefCell<Node<T>>>>::new(),edges:Vec::<Rc<RefCell<Edge<T>>>>::new()}
  }

  /// Returns true if the Graph has no Nodes, false otherwise
  pub fn is_empty(&self) -> bool
  {
    self.nodes.is_empty()
  }
  
  /// Returns true if the Graph has only one Node, false otherwise
  pub fn is_trivial(&self) -> bool
  {
    self.nodes.len()==1
  }
  
  /// Returns true if the Graph has no Edges, false otherwise
  pub fn is_edgeless(&self) -> bool
  {
    self.edges.is_empty()
  }

  /// Returns the number of Nodes in the Graph
  pub fn order(&self) -> usize
  {
    self.nodes.len()
  }
  
  /// Returns the number of Edges in the Graph
  pub fn size(&self) -> usize
  {
    self.edges.len()
  }

  /// Returns the density of the Graph
  pub fn density(&self) -> f64
  {
    if self.is_empty()||self.is_trivial() { return 0.; }
    (2*self.size()) as f64/(self.order()*(self.order()-1)) as f64
  }

  /// Create a new Node with a given value and add it to the Graph.
  /// Cannot add a new Node with the same value as a Node already in the Graph.
  /// 
  /// # Parameters
  /// * `val` : T
  ///   The value for the Node to take.
  /// 
  /// # Returns
  /// * `res` : Result<Rc<RefCell<Node<T>>>,usize>
  ///   `res` is Result::Ok if the Node was added. res::OK contains an Rc<RefCell<>> to the Node.
  ///   `res` is Result::Err if the Node already exists. res::Err contains `val`.
  pub fn add_node(&mut self,val: T) -> Result<Rc<RefCell<Node<T>>>,T>
  {
    // check the Node doesn't already exist
    if self.find(val).is_some() { return Result::Err(val); }

    // construct the Node and the result from the NOde
    let nd: Rc<RefCell<Node<T>>>=Rc::new(RefCell::new(Node::new(val)));
    let res: Result<Rc<RefCell<Node<T>>>,T>=Result::Ok(Rc::clone(&nd));
    // add the Node to the Graph
    self.nodes.push(nd);
    res
  }

  /// Connect two Nodes in the Graph.
  /// 
  /// # Parameters
  /// * `val_one`,`val_two` : T
  ///   The values of the two Nodes to connect.
  /// 
  /// # Returns
  /// * `res` : Result<Rc<RefCell<Edge<T>>>,T>
  ///   `res` is Result::Ok if the Nodes were is_connected. res::OK contains an Rc<RefCell<>> to the Edge connecting the Nodes.
  ///   `res` is Result::Err if either of the Nodes do not exist or if the Nodes are already connected. res::Err contains Option::Some if a
  ///     Node did not exist, and the value of Option::Some is the value of the first Node which did not exist. res::Err contains 
  ///     Option::None if the Nodes are already connected.
  pub fn connect(&mut self,val_one: T,val_two: T) -> Result<Rc<RefCell<Edge<T>>>,Option<T>>
  {
    // check both Nodes exist
    let nd_one: Option<Rc<RefCell<Node<T>>>>=self.find(val_one);
    if nd_one.is_none() { return Result::Err(Option::Some(val_one)); }
    let nd_two: Option<Rc<RefCell<Node<T>>>>=self.find(val_two);
    if nd_two.is_none() { return Result::Err(Option::Some(val_two)); }

    // retrieve the Nodes
    let nd_one: Rc<RefCell<Node<T>>>=nd_one.unwrap();
    let nd_two: Rc<RefCell<Node<T>>>=nd_two.unwrap();

    // check if the Nodes are already is_connected
    // but if one of them is isolated, we don't need to bother
    if !(nd_one.borrow().is_isolated()||nd_two.borrow().is_isolated())
    {
      for  connected_nd in &nd_one.borrow().adjacent_nodes().unwrap()
      {
        if nd_two.borrow().val()==connected_nd.borrow().val() { return Result::Err(Option::None); }
      }
    }

    // construct the Edge from the two Nodes and the result from the Edge
    let edge: Rc<RefCell<Edge<T>>>=Rc::new(RefCell::new(Edge{nodes:vec![Rc::clone(&nd_one),Rc::clone(&nd_two)]}));
    let res: Result<Rc<RefCell<Edge<T>>>,Option<T>>=Result::Ok(Rc::clone(&edge));
    // add the Edge to the two Nodes
    nd_one.borrow_mut().edges.push(Rc::clone(&edge));
    nd_two.borrow_mut().edges.push(Rc::clone(&edge));
    // add the Edge to the Graph
    self.edges.push(edge);
    res
  }

  /// Returns true if the Graph is connected, false otherwise
  pub fn is_connected(&self) -> bool
  {
    // trivial graph cases
    if self.is_empty() { return false; }
    if self.is_trivial() { return false; }
    if self.is_edgeless() { return false; }

    // very simple graphs
    if self.order()==2 && self.size()==1 { return true; }
    if self.order()==3 && self.size()>1 { return true; }

    // now just do a breath first search
    let mut visited: Vec<bool>=vec![false;self.order()];
    let mut q: VecDeque<Rc<RefCell<Node<T>>>>=VecDeque::<Rc<RefCell<Node<T>>>>::new();
    // add the first Noe and mark as visited
    q.push_back(Rc::clone(&self.nodes[0]));
    visited[0]=true;
    while !q.is_empty()
    {
      let nd: Rc<RefCell<Node<T>>>=q.pop_front().unwrap();
      if nd.borrow().is_isolated() { continue; }
      let nd_val: T=nd.borrow().val();
      // search all Nodes connected to the current Node
      for connected_nd in &nd.borrow().adjacent_nodes().unwrap()
      {
        // index of connected Node
        let idx: usize=self.idx(connected_nd.borrow().val()).unwrap();
        // if we haven't visited, mark as so, and add to search queue
        if !visited[idx]
        {
          visited[idx]=true;
          q.push_back(Rc::clone(&connected_nd));
        }
      }
    }
    // if all of visited is true, the Graph is connected
    visited.iter().all(|&x| x==true)
  }

  /// Find a Hamiltonian path in a Graph
  /// 
  /// # Returns
  /// * `path` : Option<Vec<Rc<RefCell<Node<T>>>>>
  ///   `path` is Option::Some if a Hamiltonian path exists. path::Some contains a Vec of the path.
  ///   `path` is Option::None if no Hamiltonian path exists.
  pub fn hamiltonian_path(&self) -> Option<Vec<Rc<RefCell<Node<T>>>>>
  {
    // the graph must be connected
    if !self.is_connected() { return Option::None; }
    
    let mut degree_one_nodes_cnt: usize=0;
    let mut first_leaf_node: usize=0;
    // the Graph cannot have more than two leaf Nodes and save the first one found
    for (itr,nd) in self.nodes.iter().enumerate()
    {
      if nd.borrow().is_leaf()
      {
        degree_one_nodes_cnt += 1;
        if first_leaf_node==0 { first_leaf_node=itr; }
      }
      if degree_one_nodes_cnt>2 { return Option::None; }
    }

    // now do a depth first search
    // either get the first leaf node or the first node
    let init_node: Rc<RefCell<Node<T>>> = Rc::clone(&self.nodes[first_leaf_node]);
    // initialise the path with the first node
    let mut path: Vec<Rc<RefCell<Node<T>>>>=Vec::<Rc<RefCell<Node<T>>>>::new();
    path.push(Rc::clone(&init_node));
    // do the search
    let res: bool=self.dfs(Rc::clone(&init_node),&mut path);

    if res { return Option::Some(path); }

    Option::None
  }

  /// Find a node in the Graph
  /// 
  /// # Parameters
  /// * `val` : T
  ///   The value of the Node to find.
  /// 
  /// # Returns
  /// * `res` : Option<Rc<RefCell<Node<T>>>>
  ///   `res` is Option::Some if the Node was found. res::Some contains an Rc<RefCell<>> to the Node.
  ///   `res` is Option::None if the Node could not be found.
  fn find(&self,val: T) -> Option<Rc<RefCell<Node<T>>>>
  {
    for nd in &self.nodes
    {
      if nd.borrow().val==val { return Option::Some(Rc::clone(&nd)); }
    }
    Option::None
  }

  /// Get the index of a node in a Graph
  /// 
  /// # Parameters
  /// * `val` : T
  ///   The value of the Node to find.
  /// 
  /// # Returns
  /// * `res` : Option<usize>
  ///   `res` is Option::Some if the Node was found. res::Some contains the index of the Node.
  ///   `res` is Option::None if the Node could not be found.
  fn idx(&self,val: T) -> Option<usize>
  {
    self.nodes.iter().position(|x| x.borrow().val()==val)
  }

  /// Depth-first search helper function for hamiltonian_path()
  fn dfs(&self,nd: Rc<RefCell<Node<T>>>,path: &mut Vec<Rc<RefCell<Node<T>>>>) -> bool
  {
    // if the path is as big as the Graph, a path has been found
    if path.len()==self.order() { return true; }
    
    // scan across all adjacent Nodes
    for adj_nd in &nd.borrow().adjacent_nodes().unwrap()
    {
      // if the adjacent Node is already in the path, ignore it: this is a hamiltonian path, after all
      if path.iter().position(|x| x.borrow().val()==adj_nd.borrow().val()).is_some() { continue; }

      // find a path off the adjacent Node just added to the path
      path.push(Rc::clone(&adj_nd));
      if self.dfs(Rc::clone(&adj_nd),path) { return true; }
      path.pop();
    }
    false
  }
}

impl<'a,T> std::iter::IntoIterator for &'a Graph<T>
  where T: Scalar
{
  type Item = &'a Rc<RefCell<Node<T>>>;
  type IntoIter = std::slice::Iter<'a,Rc<RefCell<Node<T>>>>;

  fn into_iter(self) -> std::slice::Iter<'a,Rc<RefCell<Node<T>>>>
  {
    self.nodes.iter()
  }
}

impl<T> std::fmt::Display for Graph<T>
  where T: Scalar
{
  fn fmt(&self,f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
  {
    write!(f,"Nodes:\n  ");
    for (itr,nd) in self.nodes.iter().enumerate()
    {
      write!(f,"{}",nd.borrow());
      if itr!=self.order()-1 { write!(f, ","); }
    }
    write!(f,"\nEdges:\n  ");
    for (itr,ed) in self.edges.iter().enumerate()
    {
      write!(f,"{}",ed.borrow());
      if itr!=self.size()-1 { write!(f, ",\n  "); }
    }
    write!(f,"")
  }
}

pub struct Path<T>
  where T: Scalar
{
  nodes: Vec<Rc<RefCell<Node<T>>>>,
}

impl<T> Path<T>
  where T: Scalar
{
  /// Return a new Path with an empty Vec of Nodes
  pub fn new() -> Self
  {
    Path{nodes:Vec::<Rc<RefCell<Node<T>>>>::new()}
  }

  /// Push a new Node onto the Path
  pub fn push(&mut self,nd: &Rc<RefCell<Node<T>>>)
  {
    &self.nodes.push(Rc::clone(&nd));
  }

  /// Pop the last Node off the Path
  pub fn pop(&mut self)
  {
    &self.nodes.pop();
  }
}

impl<T> std::fmt::Display for Path<T>
  where T: Scalar
{
  fn fmt(&self,f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
  {
    for (itr,nd) in self.nodes.iter().enumerate()
    {
      write!(f,"{}",nd.borrow());
      if itr!=self.nodes.len()-1 { write!(f, " -> "); }
    }
    write!(f,"")
  }
}

impl<T> std::ops::Index<usize> for Path<T>
  where T: Scalar
{
  type Output=Rc<RefCell<Node<T>>>;

  fn index(&self,ind: usize) -> &Self::Output
  {
    &self.nodes[ind]
  }
}


//
// Tests
//

#[cfg(test)]
mod node_tests
{
  use super::{Graph,Node};
  use super::{Rc,RefCell};

  #[test]
  fn test_new()
  {
    // create a bunch of Nodes with different value types and check they get set
    // and the Edge Vec is empty
    let node=Node::<i32>::new(0);
    assert!(node.val==0);
    assert!(node.edges.is_empty());

    let node=Node::<bool>::new(true);
    assert!(node.val==true);
    assert!(node.edges.is_empty());

    let node=Node::<f64>::new(3.14);
    assert!(node.val==3.14);
    assert!(node.edges.is_empty());

    let node=Node::<char>::new('c');
    assert!(node.val=='c');
    assert!(node.edges.is_empty());
  }

  #[test]
  fn test_val()
  {
    // create a bunch of Nodes with different value types and check they get set with Node::val()
    let node=Node::<i32>::new(0);
    assert!(node.val()==0);

    let node=Node::<bool>::new(true);
    assert!(node.val()==true);

    let node=Node::<f64>::new(3.14);
    assert!(node.val()==3.14);

    let node=Node::<char>::new('c');
    assert!(node.val()=='c');
  }

  #[test]
  fn test_adjacent_nodes()
  {
    let mut gr: Graph<u32>=Graph::<u32>::new();
    
    let nd_one: Rc<RefCell<Node<u32>>>=gr.add_node(6).unwrap();
    let nd_two: Rc<RefCell<Node<u32>>>=gr.add_node(28).unwrap();
    let nd_three: Rc<RefCell<Node<u32>>>=gr.add_node(496).unwrap();
    let nd_four: Rc<RefCell<Node<u32>>>=gr.add_node(8128).unwrap();
    
    // check before connections that each Node has no adjacent Nodes
    assert!(nd_one.borrow().adjacent_nodes().is_none());
    assert!(nd_two.borrow().adjacent_nodes().is_none());
    assert!(nd_three.borrow().adjacent_nodes().is_none());
    assert!(nd_four.borrow().adjacent_nodes().is_none());

    // connecting a Node returns Some
    gr.connect(6,28);
    assert!(nd_one.borrow().adjacent_nodes().is_some());
    // connecting another Node returns Some
    gr.connect(6,496);
    assert!(nd_one.borrow().adjacent_nodes().is_some());
    
    // the connected Nodes are in the Vec
    // the not connected Node is not
    // the Node itself is not either
    let adj: Vec<Rc<RefCell<Node<u32>>>>=nd_one.borrow().adjacent_nodes().unwrap();
    assert!(adj.contains(&nd_two));
    assert!(adj.contains(&nd_three));
    assert!(!adj.contains(&nd_four));
    assert!(!adj.contains(&nd_one));
  }

  #[test]
  fn test_degree()
  {
    let mut gr: Graph<u32>=Graph::<u32>::new();
    
    let nd_one: Rc<RefCell<Node<u32>>>=gr.add_node(6).unwrap();
    let nd_two: Rc<RefCell<Node<u32>>>=gr.add_node(28).unwrap();
    let nd_three: Rc<RefCell<Node<u32>>>=gr.add_node(496).unwrap();
    let nd_four: Rc<RefCell<Node<u32>>>=gr.add_node(8128).unwrap();
    let nd_five: Rc<RefCell<Node<u32>>>=gr.add_node(33550336).unwrap();

    let val: [u32;3]=[28,496,8128];

    // check before connections that each Node has degree 0
    assert!(nd_one.borrow().degree()==0);
    assert!(nd_two.borrow().degree()==0);
    assert!(nd_three.borrow().degree()==0);
    assert!(nd_four.borrow().degree()==0);
    assert!(nd_five.borrow().degree()==0);

    let nd_two_degrs: [u32;3]=[1,1,1];
    let nd_three_degrs: [u32;3]=[0,1,1];
    let nd_four_degrs: [u32;3]=[0,0,1];

    // connect Nodes two through four
    for itr in 0..3
    {
      gr.connect(6,val[itr]);
      // connecting a Node increments their degree, leaves the others
      assert!(nd_one.borrow().degree()==itr+1);
      assert!(nd_two.borrow().degree()==nd_two_degrs[itr] as usize);
      assert!(nd_three.borrow().degree()==nd_three_degrs[itr] as usize);
      assert!(nd_four.borrow().degree()==nd_four_degrs[itr] as usize);
      assert!(nd_five.borrow().degree()==0);
    }
  }
  
  #[test]
  fn test_is_isolated()
  {
    let mut gr: Graph<u32>=Graph::<u32>::new();
    
    let nd_one: Rc<RefCell<Node<u32>>>=gr.add_node(6).unwrap();
    assert!(nd_one.borrow().is_isolated());
    // adding Nodes keeps is isoalted
    let nd_two: Rc<RefCell<Node<u32>>>=gr.add_node(28).unwrap();
    assert!(nd_one.borrow().is_isolated());
    let nd_three: Rc<RefCell<Node<u32>>>=gr.add_node(496).unwrap();
    assert!(nd_one.borrow().is_isolated());
    
    // connecting the other Nodes keeps it isolated
    gr.connect(496,28);
    assert!(nd_one.borrow().is_isolated());
    
    // connecting the Node removes isolation
    gr.connect(6,28);
    assert!(!nd_one.borrow().is_isolated());
    gr.connect(6,496);
    assert!(!nd_one.borrow().is_isolated());
  }

  #[test]
  fn test_is_leaf()
  {
    let mut gr: Graph<u32>=Graph::<u32>::new();
    
    let nd_one: Rc<RefCell<Node<u32>>>=gr.add_node(6).unwrap();
    assert!(!nd_one.borrow().is_leaf());
    // adding Nodes keeps it not a leaf Node
    let nd_two: Rc<RefCell<Node<u32>>>=gr.add_node(28).unwrap();
    assert!(!nd_one.borrow().is_leaf());
    let nd_three: Rc<RefCell<Node<u32>>>=gr.add_node(496).unwrap();
    assert!(!nd_one.borrow().is_leaf());
    
    // connecting the other Nodes keeps it not a leaf Node
    gr.connect(496,28);
    assert!(!nd_one.borrow().is_leaf());
    
    // connecting the Node makes it a leaf Node
    gr.connect(6,28);
    assert!(nd_one.borrow().is_leaf());
    // connecting to the other Node makes it not a leaf Node again
    gr.connect(6,496);
    assert!(!nd_one.borrow().is_leaf());
  }
  
  #[test]
  fn test_eq()
  {
    let nd_one: Node<char>=Node::<char>::new('a');
    let nd_two: Node<char>=Node::<char>::new('b');
    let nd_three: Node<char>=Node::<char>::new('a');

    // test equal when values are the same
    assert!(nd_one==nd_one);
    assert!(nd_one==nd_three);

    // test not equal when values differ
    assert!(nd_one!=nd_two);
    assert!(nd_three!=nd_two);
  }
}

#[cfg(test)]
mod graph_tests
{
  use super::{Rc,Option,Result,RefCell};
  use super::{Graph,Node,Edge};

  #[test]
  fn test_new()
  {
    let gr=Graph::<usize>::new();
    // test a new Graph has no Nodes or Edges
    assert!(gr.nodes.is_empty());
    assert!(gr.edges.is_empty());
  }

  #[test]
  fn test_is_empty()
  {
    let mut gr: Graph<f64>=Graph::<f64>::new();
    // a new Graph is empty
    assert!(gr.is_empty());

    gr.add_node(3.14);
    // adding a Node makes it not empty
    assert!(!gr.is_empty());
  }

  #[test]
  fn test_is_trivial()
  {
    let mut gr: Graph<f64>=Graph::<f64>::new();
    // an empty Graph is not trivial
    assert!(!gr.is_trivial());

    gr.add_node(3.14);
    // adding one Node makes it trivial
    assert!(gr.is_trivial());

    gr.add_node(1.618);
    // adding a second Node makes it no longer trivial
    assert!(!gr.is_trivial());
  }

  #[test]
  fn test_is_edgeless()
  {
    let mut gr: Graph<f64>=Graph::<f64>::new();
    // empty Graph is edgeless
    assert!(gr.is_edgeless());
    // continuously adding Nodes without connecting them keeps it edgeless
    gr.add_node(3.14);
    assert!(gr.is_edgeless());
    gr.add_node(1.618);
    assert!(gr.is_edgeless());
    gr.add_node(2.718);
    assert!(gr.is_edgeless());
    gr.add_node(-0.083);
    assert!(gr.is_edgeless());
    
    // making connections makes it not edgeless
    gr.connect(3.14,2.718);
    assert!(!gr.is_edgeless());
    gr.connect(3.14,1.618);
    assert!(!gr.is_edgeless());
  }

  #[test]
  fn test_order()
  {
    // test the order increments as we add Nodes
    let mut gr: Graph<f64>=Graph::<f64>::new();
    // empty Graph has order 0
    assert!(gr.order()==0);

    gr.add_node(3.14);
    assert!(gr.order()==1);

    gr.add_node(1.618);
    assert!(gr.order()==2);
    
    // making a connection doesn't affect the order
    gr.connect(3.14,1.618);
    assert!(gr.order()==2);
  }

  #[test]
  fn test_size()
  {
    let mut gr: Graph<f64>=Graph::<f64>::new();
    // empty Graph has size 0
    assert!(gr.size()==0);
    // test adding Nodes does not affect size
    gr.add_node(3.14);
    assert!(gr.size()==0);
    gr.add_node(1.618);
    assert!(gr.size()==0);
    gr.add_node(2.718);
    assert!(gr.size()==0);
    gr.add_node(-0.083);
    assert!(gr.size()==0);
    
    // adding connections increments the size
    gr.connect(3.14,2.718);
    assert!(gr.size()==1);
    gr.connect(3.14,1.618);
    assert!(gr.size()==2);
    gr.connect(1.618,-0.083);
    assert!(gr.size()==3);
  }

  #[test]
  fn test_density()
  {
    let mut gr: Graph<f64>=Graph::<f64>::new();
    // empty Graph has density 0
    assert!(gr.density()==0.);
    // test adding one Node does not affect density
    gr.add_node(3.14);
    assert!(gr.density()==0.);
    // test adding another Node does not affect density
    gr.add_node(1.618);
    gr.connect(3.14,1.618);
    // connecting the two Nodes gives density 1
    assert!(gr.density()==1.);
    
    // test various other simple configurations
    gr.add_node(2.718);
    assert!(gr.density()==1./3.);
    gr.add_node(-0.083);  
    assert!(gr.density()==1./6.);
    gr.connect(3.14,2.718);
    assert!(gr.density()==1./3.);
    gr.connect(1.618,-0.083);
    assert!(gr.density()==1./2.);
  }

  #[test]
  fn test_add_node()
  {
    // test a valid insertion
    let mut gr=Graph::<usize>::new();
    let res: Result<Rc<RefCell<Node<usize>>>,usize>=gr.add_node(2);
    assert!(res.is_ok());
    assert!(res.unwrap().borrow().val==2);
    assert!(gr.nodes[0].borrow().val==2);
    assert!(gr.nodes.len()==1);
    
    // test an invalid insertion
    let res: Result<Rc<RefCell<Node<usize>>>,usize>=gr.add_node(2);
    assert!(res.is_err());
    assert!(res.err().unwrap()==2);
    assert!(gr.nodes.len()==1);
    
    // test another valid insertion
    let res: Result<Rc<RefCell<Node<usize>>>,usize>=gr.add_node(1729);
    assert!(res.is_ok());
    assert!(res.unwrap().borrow().val==1729);
    assert!(gr.nodes.len()==2);
    assert!(gr.nodes[1].borrow().val==1729);
  }

  #[test]
  fn test_connect()
  {
    // test error when no nodes are added
    let mut gr=Graph::<i32>::new();
    let res: Result<Rc<RefCell<Edge<i32>>>,Option<i32>>=gr.connect(173,-98);
    assert!(res.is_err());
    // the Err Result should be the first value
    assert!(res.err().unwrap().unwrap()==173);
    assert!(gr.edges.is_empty());
    
    // test error when one node has been added
    let nd_one: Rc<RefCell<Node<i32>>>=gr.add_node(173).unwrap();
    let res: Result<Rc<RefCell<Edge<i32>>>,Option<i32>>=gr.connect(173,-98);
    assert!(res.is_err());
    // the Err Result should be the second value
    assert!(res.err().unwrap().unwrap()==-98);
    assert!(gr.edges.is_empty());

    // test no error when both nodes have been added
    let nd_two: Rc<RefCell<Node<i32>>>=gr.add_node(-98).unwrap();
    let res: Result<Rc<RefCell<Edge<i32>>>,Option<i32>>=gr.connect(173,-98);
    assert!(gr.edges.len()==1); // one edge should have been added
    assert!(res.is_ok()); // Result should be Ok
    let edge_one: Rc<RefCell<Edge<i32>>>=res.unwrap();
    // Nodes should have been added to Edge in order
    assert!(&*nd_one.borrow() as *const Node<i32> == &*edge_one.borrow().nodes[0].borrow() as *const Node<i32>);
    assert!(&*nd_two.borrow() as *const Node<i32> == &*edge_one.borrow().nodes[1].borrow() as *const Node<i32>);
    
    // test no error when both nodes have been added
    let nd_three: Rc<RefCell<Node<i32>>>=gr.add_node(1).unwrap();
    let res: Result<Rc<RefCell<Edge<i32>>>,Option<i32>>=gr.connect(173,1);
    assert!(gr.edges.len()==2); // one edge should have been added
    assert!(res.is_ok()); // Result should be Ok
    let edge_two: Rc<RefCell<Edge<i32>>>=res.unwrap();
    // Nodes should have been added to Edge in order
    assert!(&*nd_one.borrow() as *const Node<i32> == &*edge_two.borrow().nodes[0].borrow() as *const Node<i32>);
    assert!(&*nd_three.borrow() as *const Node<i32> == &*edge_two.borrow().nodes[1].borrow() as *const Node<i32>);

    // check matches
    assert!(&*gr.nodes[0].borrow() as *const Node<i32> == &*gr.edges[0].borrow().nodes[0].borrow() as *const Node<i32>); 
    assert!(&*gr.nodes[0].borrow() as *const Node<i32> == &*gr.edges[1].borrow().nodes[0].borrow() as *const Node<i32>); 
    assert!(&*gr.nodes[1].borrow() as *const Node<i32> == &*gr.edges[0].borrow().nodes[1].borrow() as *const Node<i32>); 
    assert!(&*gr.nodes[2].borrow() as *const Node<i32> == &*gr.edges[1].borrow().nodes[1].borrow() as *const Node<i32>);

    // check matches
    assert!(&*nd_one.borrow().edges[0].borrow() as *const Edge<i32> == &*edge_one.borrow()  as *const Edge<i32>);
    assert!(&*nd_one.borrow().edges[1].borrow() as *const Edge<i32> == &*edge_two.borrow()  as *const Edge<i32>);
    assert!(&*nd_two.borrow().edges[0].borrow() as *const Edge<i32> == &*edge_one.borrow()  as *const Edge<i32>);
    assert!(&*nd_three.borrow().edges[0].borrow() as *const Edge<i32> == &*edge_two.borrow()  as *const Edge<i32>);

    // test error when trying to connect already connected Nodes
    let res: Result<Rc<RefCell<Edge<i32>>>,Option<i32>>=gr.connect(173,-98);
    assert!(res.is_err());
    // the Err Result should be the first value
    assert!(res.err().unwrap()==Option::None);
    assert!(gr.edges.len()==2);
    // and the other way around
    let res: Result<Rc<RefCell<Edge<i32>>>,Option<i32>>=gr.connect(-98,173);
    assert!(res.is_err());
    // the Err Result should be the first value
    assert!(res.err().unwrap()==Option::None);
    assert!(gr.edges.len()==2);
  }

  #[test]
  fn test_is_connected()
  {
    let mut gr: Graph<i32>=Graph::<i32>::new();
    // an empty Graph is not connected
    assert!(!gr.is_connected());
    gr.add_node(10858);
    // a trivial Graph is not connected
    assert!(!gr.is_connected());

    // add a new Node
    gr.add_node(8191);
    assert!(!gr.is_connected());
    gr.connect(10858,8191);
    // connecting the two makes the Graph connected
    assert!(gr.is_connected());
    gr.add_node(78557);
    // adding a third Node makes the Graph disconnected
    assert!(!gr.is_connected());

    // progressively add new Nodes and connections and test connectedness
    gr.connect(78557,10858);
    assert!(gr.is_connected());
    gr.add_node(6);
    gr.connect(78557,8191);
    assert!(!gr.is_connected());
    gr.connect(10858,6);
    assert!(gr.is_connected());
    gr.add_node(1729);
    assert!(!gr.is_connected());
    gr.add_node(30357);
    assert!(!gr.is_connected());
    gr.connect(1729,30357);
    assert!(!gr.is_connected());
  }

  #[test]
  fn test_hamiltonian_path()
  {
    let mut gr: Graph<f64>=Graph::<f64>::new();
    gr.add_node(3.14);
    gr.add_node(1.618);
    gr.add_node(2.718);
    gr.add_node(-0.083);
    assert!(gr.hamiltonian_path().is_none());
    gr.connect(3.14,1.618);
    gr.connect(-0.083,1.618);
    gr.connect(2.718,1.618);
    assert!(gr.hamiltonian_path().is_none());
    gr.connect(2.718,-0.083);
    assert!(gr.hamiltonian_path().is_some());
  }

  #[test]
  fn test_find()
  {
    let vals: [f64;5]=[3.14,2.72,1.20,1.62,1.64];
    let mut gr=Graph::<f64>::new();
    
    // add the values
    for &val in vals.iter()
    {
      gr.add_node(val);
    }
    // values that have been added can be found
    for &val in vals.iter()
    {
      let res: Option<Rc<RefCell<Node<f64>>>>=gr.find(val);
      assert!(res.is_some());
      let nd: Rc<RefCell<Node<f64>>>=res.unwrap();
      assert!(nd.borrow().val==val);
    }
    // a value that hasn't been added cannot be found
    let res: Option<Rc<RefCell<Node<f64>>>>=gr.find(2.93);
    assert!(res.is_none());
  }

  #[test]
  fn test_idx()
  {
    let vals: [f64;5]=[3.14,2.72,1.20,1.62,1.64];
    let mut gr=Graph::<f64>::new();
    
    // add the values
    for &val in vals.iter()
    {
      gr.add_node(val);
    }
    // values that have been added have the correct index
    for (itr,&val) in vals.iter().enumerate()
    {
      let res: Option<usize>=gr.idx(val);
      assert!(res.is_some());
      assert!(res.unwrap()==itr);
    }
    // a value that hasn't been added has no index
    let res: Option<usize>=gr.idx(2.93);
    assert!(res.is_none());
  }

  #[test]
  fn test_dfs()
  {
    // we don't need to test for empty, trivial, or edgeless Graphs, as the hamiltonian_path() checks for that, and dfs() is not public
    let mut gr: Graph<char>=Graph::<char>::new();
    let mut path: Vec<Rc<RefCell<Node<char>>>>=Vec::<Rc<RefCell<Node<char>>>>::new();
    
    let nd_one: Rc<RefCell<Node<char>>>=gr.add_node('a').unwrap();
    let nd_two: Rc<RefCell<Node<char>>>=gr.add_node('b').unwrap();
    
    // connecting Nodes one and two makes a path
    gr.connect('a','b');
    assert!(gr.dfs(Rc::clone(&nd_one),&mut path));
    assert!(path[0].borrow().val=='b');
    assert!(path[1].borrow().val=='a');
    
    // adding on a third Node makes a path
    let mut path: Vec<Rc<RefCell<Node<char>>>>=Vec::<Rc<RefCell<Node<char>>>>::new();
    let nd_three: Rc<RefCell<Node<char>>>=gr.add_node('c').unwrap();
    gr.connect('a','c');
    assert!(gr.dfs(Rc::clone(&nd_one),&mut path));
    assert!(path[0].borrow().val=='b');
    assert!(path[1].borrow().val=='a');
    assert!(path[2].borrow().val=='c');
    
    // adding on a fourth Node at first breaks the path
    let mut path: Vec<Rc<RefCell<Node<char>>>>=Vec::<Rc<RefCell<Node<char>>>>::new();
    let nd_four: Rc<RefCell<Node<char>>>=gr.add_node('d').unwrap();
    gr.connect('a','d');
    assert!(!gr.dfs(Rc::clone(&nd_one),&mut path));
    // but connecting it up properly makes the path again
    gr.connect('b','d');
    assert!(gr.dfs(Rc::clone(&nd_one),&mut path));
    assert!(path[0].borrow().val=='b');
    assert!(path[1].borrow().val=='d');
    assert!(path[2].borrow().val=='a');
    assert!(path[3].borrow().val=='c');
  }

  #[test]
  fn test_iter()
  {
    let mut gr: Graph<char>=Graph::<char>::new();
    let vals: [char;4]=['a','b','c','z'];
    
    // add the values
    for val in vals.into_iter()
    {
      gr.add_node(*val);
    }

    // iterating the Graph gives the values in the order added
    let mut itr: usize=0;
    for nd in gr.into_iter()
    {
      assert!(nd.borrow().val==vals[itr]);
      itr+=1;
    }
    // (compile time?) test that the iter doesn't move the Graph
    gr.add_node('y');
  }
}

#[cfg(test)]
mod path_tests
{
  use super::{Path,Node,Rc,RefCell};
  
  #[test]
  fn test_new()
  {
    // test a new Path has no Nodes
    let p: Path<i32>=Path::<i32>::new();
    assert!(p.nodes.len()==0);
  }
  
  #[test]
  fn test_push()
  {
    let mut p: Path<f64>=Path::<f64>::new();
    
    let nd_one: Rc<RefCell<Node<f64>>>=Rc::new(RefCell::new(Node::new(0.11)));
    let nd_two: Rc<RefCell<Node<f64>>>=Rc::new(RefCell::new(Node::new(2.718)));
    let nd_three: Rc<RefCell<Node<f64>>>=Rc::new(RefCell::new(Node::new(3.14)));

    p.push(&nd_one);
    p.push(&nd_two);
    p.push(&nd_three);

    // check the Nodes have been added
    assert!(&*p.nodes[0].borrow() as *const Node<f64> == &*nd_one.borrow() as *const Node<f64>);
    assert!(&*p.nodes[1].borrow() as *const Node<f64> == &*nd_two.borrow() as *const Node<f64>);
    assert!(&*p.nodes[2].borrow() as *const Node<f64> == &*nd_three.borrow() as *const Node<f64>);
  }

  #[test]
  fn test_pop()
  {
    let mut p: Path<f64>=Path::<f64>::new();
    
    let nd_one: Rc<RefCell<Node<f64>>>=Rc::new(RefCell::new(Node::new(0.11)));
    let nd_two: Rc<RefCell<Node<f64>>>=Rc::new(RefCell::new(Node::new(2.718)));
    let nd_three: Rc<RefCell<Node<f64>>>=Rc::new(RefCell::new(Node::new(3.14)));

    p.push(&nd_one);
    p.push(&nd_two);
    p.push(&nd_three);

    // test popping decreases the length
    assert!(p.nodes.len()==3);
    p.pop();
    assert!(p.nodes.len()==2);
    p.pop();
    assert!(p.nodes.len()==1);
    p.pop();
    assert!(p.nodes.len()==0);
  }

  #[test]
  fn test_index()
  {
    let mut p: Path<f64>=Path::<f64>::new();
    
    let nd_one: Rc<RefCell<Node<f64>>>=Rc::new(RefCell::new(Node::new(0.11)));
    let nd_two: Rc<RefCell<Node<f64>>>=Rc::new(RefCell::new(Node::new(2.718)));
    let nd_three: Rc<RefCell<Node<f64>>>=Rc::new(RefCell::new(Node::new(3.14)));

    p.push(&nd_one);
    p.push(&nd_two);
    p.push(&nd_three);

    // check the Nodes have been added
    assert!(&*p[0].borrow() as *const Node<f64> == &*nd_one.borrow() as *const Node<f64>);
    assert!(&*p[1].borrow() as *const Node<f64> == &*nd_two.borrow() as *const Node<f64>);
    assert!(&*p[2].borrow() as *const Node<f64> == &*nd_three.borrow() as *const Node<f64>);
  }
}
