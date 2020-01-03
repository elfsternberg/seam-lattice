![Language: Rust](https://img.shields.io/badge/language-Rust-green.svg)
![Topic: Graphs](https://img.shields.io/badge/topic-Graphs-red.svg)
![Library Status: Alpha](https://img.shields.io/badge/status-Library_Complete-red.svg)

# Seams, Grids, and Lattices

This library takes in a Rust Vector that represents a two-dimensional
space, and converts that Vec into a graph of points with ways to
navigate from one point to another.

## Purpose

`seam-lattice` exists to support my
[seamcarving](https://github.com/elfsternberg/pamseam-rs) library of
functions.  It provides a standardized API for accessing individual
points, rows, and columns, and tracks the removal of seams.  It can take
a visitor to perform these operations, and return the modified visitor.

By making the _analysis_ phase of a seam operation a read-only
pass, we make it easier to multi-thread, and by turning the grid into a
lattice, we make the recalculation of the grid much faster.  An
individual pass will be slower than a grid-based solution, but multiple
passes are expected to be faster.

## Acceptable cons

Traversing to an individual cell (x, y) requires O(n), where 'n' is the
size of the board, whereas in a grid that traversal only takes O(1).  On
the other hand, traversing the whole grid is an O(n) operation in either
case.

The traversal mechanism requires a *lot* of memory.  Even using 32-bit
indices, a grid requires 32 *bytes* of RAM for each cell just to track
its neighbors.  A 64MB RAW image blows up to 512MB when placed in
seamlattice.

## LICENCE

Seam-Lattice is Copyright [Elf M. Sternberg](https://elfsternberg.com)
(c) 2020, and licensed with the Mozilla Public License vers. 2.0.  A
copy of the license file is included in the root folder.

