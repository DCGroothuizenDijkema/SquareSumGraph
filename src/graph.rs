
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

#[cfg(test)]
mod node_tests {
  use super::*;

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