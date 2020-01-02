
//+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+//
//                                                                                                                                       //
// graph.rs                                                                                                                              //
//                                                                                                                                       //
// D. C. Groothuizen Dijkema - January, 2020                                                                                             //
//+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+//

// Graph theory related classes, traits, and impls


#![allow(dead_code)]

//
// Traits
//

pub trait Scalar:
  std::cmp::PartialEq
  + std::marker::Copy
{
}

impl<T> Scalar for T where T:
  std::cmp::PartialEq
  + std::marker::Copy
{
}


//
// Structs
//

struct Node<'a,T>
  where T: Scalar
{
  val: T,
  edges: std::vec::Vec<&'a Edge<'a,T>>
}

impl<'a,T> Node<'a,T>
  where T: Scalar
{
  fn new(val: T) -> Self
  {
    Node{val:val,edges:std::vec::Vec::<&'a Edge<'a,T>>::new()}
  }
}

struct Edge<'a,T>
  where T: Scalar
  {
    nodes: std::vec::Vec<&'a Node<'a,T>>
}

pub struct Graph<'a,T>
  where T: Scalar
{
  nodes: std::vec::Vec<Node<'a,T>>,
  edges: std::vec::Vec<Edge<'a,T>>,
}

impl<'a,T> Graph<'a,T>
  where T: Scalar
{
  fn new() -> Self
  {
    Graph{nodes:std::vec::Vec::<Node<'a,T>>::new(),edges:std::vec::Vec::<Edge<'a,T>>::new()}
  }

  fn add_node(&mut self,val: T) -> std::result::Result<T,usize>
  {
    for node in &self.nodes
    {
      if node.val==val { return std::result::Result::Err(1); }
    }
    self.nodes.push(Node::new(val));
    std::result::Result::Ok(val)
  }

  fn connect(&mut self,val_one: T,val_two: T) -> std::result::Result<usize,T>
  {
    if self.find(val_one).is_none() { return std::result::Result::Err(val_one); }
    if self.find(val_two).is_none() { return std::result::Result::Err(val_two); }
    std::result::Result::Ok(0)
  }

  fn find(&mut self,val: T) -> std::option::Option<&Node<T>>
  {
    for node in &self.nodes
    {
      if node.val==val { return std::option::Option::Some(node); }
    }
    std::option::Option::None
  }
}


//
// Tests
//

#[cfg(test)]
mod node_tests
{
  use super::Node;

  #[test]
  fn test_new()
  {
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
}

#[cfg(test)]
mod graph_tests
{
  use super::{Graph,Node};

  #[test]
  fn test_new()
  {
    let graph=Graph::<usize>::new();
    assert!(graph.nodes.is_empty());
    assert!(graph.edges.is_empty());
  }

  #[test]
  fn test_add_node()
  {
    // test a valid insertion
    let mut graph=Graph::<usize>::new();
    let res: std::result::Result<usize,usize>=graph.add_node(2);
    assert!(res.is_ok());
    match res
    {
      Ok(x) => assert!(x==2),
      _     => (),
    }
    assert!(graph.nodes[0].val==2);
    assert!(graph.nodes.len()==1);
    
    // test an invalid insertion
    let res: std::result::Result<usize,usize>=graph.add_node(2);
    assert!(res.is_err());
    match res
    {
      Err(x) => assert!(x==1),
      _     => (),
    }
    assert!(graph.nodes.len()==1);

    // test another valid insertion
    let res: std::result::Result<usize,usize>=graph.add_node(1729);
    assert!(res.is_ok());
    match res
    {
      Ok(x) => assert!(x==1729),
      _     => (),
    }
    assert!(graph.nodes.len()==2);
    assert!(graph.nodes[1].val==1729);
  }

  #[test]
  fn test_find()
  {
    let vals: [f64;5]=[3.14,2.72,1.20,1.62,1.64];
    let mut graph=Graph::<f64>::new();
    
    // add the values
    for &val in vals.iter()
    {
      graph.add_node(val).unwrap();
    }
    // values that have been added can be found
    for &val in vals.iter()
    {
      let res: std::option::Option<&Node<f64>>=graph.find(val);
      assert!(res.is_some());
      let nd: &Node<f64>=res.unwrap();
      assert!(nd.val==val);
    }
    // a value that hasn't been added cannot be found
    let res: std::option::Option<&Node<f64>>=graph.find(2.93);
    assert!(res.is_none());
  }

  #[test]
  fn test_connect()
  {
    // test error
    let mut graph=Graph::<i32>::new();
    let res: std::result::Result<usize,i32>=graph.connect(173,-98);
    assert!(res.is_err());
    match res
    {
      Err(x) => assert!(x==173),
      _      => (),
    }
    assert!(graph.edges.is_empty());
    graph.add_node(173).unwrap();
    let res: std::result::Result<usize,i32>=graph.connect(173,-98);
    assert!(res.is_err());
    match res
    {
      Err(x) => assert!(x==-98),
      _      => (),
    }
    assert!(graph.edges.is_empty());
    graph.add_node(-98).unwrap();
    let res: std::result::Result<usize,i32>=graph.connect(173,-98);
    assert!(res.is_ok());
    match res
    {
      Ok(x) => assert!(x==0),
      _     => (),
    }
  }
}