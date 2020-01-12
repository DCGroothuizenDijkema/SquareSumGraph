
# SquareSumGraph

A Solution to the Square-Sum Problem

## Problem

This programme was written after watching [a video](https://www.youtube.com/watch?v=G1m7goLCJDY) made by [Brady Haran](https://www.numberphile.com/) for [Numberphile](https://www.youtube.com/user/numberphile). The problem, presented by [Matt Parker](https://www.youtube.com/user/standupmaths) ([standupmaths](http://standupmaths.com/)), is to list all natural numbers from 1 to 15 in such a way that every consecutive pair of numbers sum to a square number. This is the first natural number for which this is possible. The video goes on to note that producing such a square-sum list is not possible for 18 through 22, but becomes possible again for 23. A [subsequent video](https://www.youtube.com/watch?v=7_ph5djCCnM) notes that it is not possible for 24, but is then possible again up to 299.

## Solution

One method to solve this problem is to produce a graph where each node is a natural number up to the given natural number, and where edges connect natural numbers which sum to a square number. Finding a Hamiltonian path through the graph will then provide the necessary square-sum list.

This Rust crate defines graph theory related structs and methods, and includes functions to produce square-sum graphs and find Hamiltonian paths through them.
