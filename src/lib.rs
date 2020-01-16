#![deny(missing_docs)]
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! SeamLattice
//!
//! The SeamLattice takes a two-dimensional

use std::default::Default;
use std::ops::{Index, IndexMut};

// Conventions!
//
// We always, *ALWAYS*, refer to width, height, in that order.  The
// position of a node on a _grid_ is therefore always `y * width + x`,
// that is, the number of rows DOWN is calculated as an offset
// multiple of the width (the maximal `x`), followed by the offset
// into the row to find the node.
//
// For navigation, we always, *ALWAYS*, talk about movement along the
// X-axis first, then the Y-axis second.
//
// Following the standard mental model for grids, the upper-left-hand
// corner is the origin, and all calculations thereafter progress
// RIGHT or DOWN, and the offsets in those directions are positive.
// Going UP or LEFT is a negative direction.
//
// The eight-cell collection of node pointers skips the center, but
// otherwise follows a predictable course from top to bottom, left to
// right.

const UP: i32 = -1;
const DN: i32 = 1;
const LF: i32 = -1;
const RT: i32 = 1;
const SM: i32 = 0;

#[allow(unused_macros)]
macro_rules! dm {
	(LF, UP) => {
			0
	};
	(SM, UP) => {
			1
	};
	(RT, UP) => {
			2
	};
	(LF, SM) => {
			3
	};
	(RT, SM) => {
			4
	};
	(LF, DN) => {
			5
	};
	(SM, DN) => {
			6
	};
	(RT, DN) => {
			7
	};
}

/// Given a general direction from one of the CONST elements above,
/// translate that into a location in the node's "neighbor" array,
/// which in turn gives us the location of that neighbor in the
/// arena.
pub fn dm(y: i32, x: i32) -> u32 {
	match (y, x) {
		(LF, UP) => 0,
		(SM, UP) => 1,
		(RT, UP) => 2,
		(LF, SM) => 3,
		(RT, SM) => 4,
		(LF, DN) => 5,
		(SM, DN) => 6,
		(RT, DN) => 7,
		_ => panic!("This should not happen"),
	}
}

#[derive(Debug, Default, Clone)]
/// Abstract Node in the Lattice; knows only what data you give it,
/// plus information about the neighbors that should really be
/// private.
pub(in crate) struct Node<P>
where
	P: std::default::Default + Copy,
{
	neighbors: [u32; 8],
	/// User-accessible information.
	pub data: P,
}

type NodeId = u32;

/// The base class for this library.  
pub struct SeamLattice<P: Default + Copy> {
	width: u32,
	height: u32,
	root: NodeId,
	data: Vec<Node<P>>,
}

// Private, obviously.  Assumes the vector will be a 1:1
// representation of the source data, such that an image could be
// reconstructed when finished.
fn initialize_lattice<P: Default + Copy>(width: u32, height: u32, data: &mut Vec<Node<P>>) {
	let mw = width - 1;
	let mh = height - 1;

	for h in 0..height {
		for w in 0..width {
			for hstep in UP..=DN {
				for wstep in LF..=RT {
					if hstep == 0 && wstep == 0 {
						continue;
					}
					let pos = (h as usize) * (width as usize) + (w as usize);
					let node_ptr = dm(wstep, hstep);
					data[pos].neighbors[node_ptr as usize] = {
						let hpoint = (h as i32) + hstep;
						let wpoint = (w as i32) + wstep;
						if hpoint < 0 || hpoint > mh as i32 || wpoint < 0 || wpoint > mw as i32 {
							pos as u32
						} else {
							width * (hpoint as u32) + (wpoint as u32)
						}
					};
				}
			}
		}
	}
}

impl<P: Default + Copy> SeamLattice<P> {
	/// Build a new empty Lattice
	pub fn new(width: u32, height: u32) -> Self {
		let mut data = vec![Node::<P>::default(); width as usize * height as usize];
		initialize_lattice(width, height, &mut data);
		SeamLattice {
			width,
			height,
			root: 0,
			data,
		}
	}

	/// Build a lattice from a source vector.  As this assumes a two-dimensional
	/// space, the width and height of the source must be included.
	pub fn create_from_grid(width: u32, height: u32, source: &Vec<P>) -> Self {
		let mut data = vec![Node::<P>::default(); width as usize * height as usize];
		initialize_lattice(width, height, &mut data);
		(0..(width * height) as usize).for_each(|i| {
			data[i].data = source[i];
		});
		SeamLattice {
			width,
			height,
			root: 0,
			data,
		}
	}

	/// Get the address of a connected node using a cardinal direction.
	pub fn transit_by_direction(&self, node: u32, direction: u32) -> NodeId {
		self.data[node as usize].neighbors[direction as usize]
	}

	/// Get the address of a connected node by specifying the vertical
	/// and horizontal directions.
	pub fn transit(&self, node: u32, x: i32, y: i32) -> NodeId {
		self.transit_by_direction(node, dm(x, y))
	}
}

impl<P: Default + Copy> Index<u32> for SeamLattice<P> {
	type Output = P;

	/// A convenience addressing mode for getting values.
	fn index(&self, p: NodeId) -> &P {
		&self.data[p as usize].data
	}
}

impl<P: Default + Copy> IndexMut<u32> for SeamLattice<P> {
	/// A convenience addressing mode for setting values.
	fn index_mut(&mut self, p: u32) -> &mut P {
		&mut self.data[p as usize].data
	}
}

impl<P: Default + Copy + std::fmt::Debug> std::fmt::Debug for SeamLattice<P> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		writeln!(
			f,
			"SeamLattice {{ width: {}, height: {}, root: {}",
			self.width, self.height, self.root
		)
		.unwrap();
		for i in &self.data {
			writeln!(f, "    {:?}", i).unwrap();
		}
		writeln!(f, "}}")
	}
}

/// This trait takes a lattice and returns a new NodeId, indicating
/// where the next step should be.
pub trait WalkStep<P: Default + Copy> {
	/// Given a lattice, return the address found by taking a step.
	fn step(&mut self, lattice: &SeamLattice<P>) -> Option<NodeId>;
}

/// A walker takes a Step (which must understandably last at least as
/// long as the Walker), and for each call of `next()` returns the
/// content of the node indicated by Step (`Some(P)`), or `None`.
pub struct Walker<P: Default + Copy> {
	prev_node_id: Option<NodeId>,
	step: Box<dyn WalkStep<P>>,
}

impl<'a, P: Default + Copy + std::fmt::Display> Walker<P> {
	/// Construct a new Walker.
	pub fn new(step: Box<dyn WalkStep<P>>) -> Walker<P> {
		Walker {
			prev_node_id: None,
			step,
		}
	}
	/// Given a lattice, return the value found at that location, or None
	/// if either the Step or the Visit indicate the end of a scan.
	pub fn next(&mut self, lattice: &'a SeamLattice<P>) -> Option<&'a P> {
		let node_id = self.step.step(&lattice);
		match node_id {
			None => None,
			Some(node_id) => {
				if let Some(prev_node_id) = self.prev_node_id {
					if prev_node_id == node_id {
						return None;
					}
				}
				let data = &lattice.data[node_id as usize].data;
				self.prev_node_id = Some(node_id);
				println!("{}", data);
				Some(data)
			}
		}
	}

	/// Given a lattice, return a reference to the value found at that location,
	/// in a mutable fashion.
	pub fn next_mut(&mut self, lattice: &'a mut SeamLattice<P>) -> Option<&'a mut P> {
		let node_id = self.step.step(&lattice);
		match node_id {
			None => None,
			Some(node_id) => {
				if let Some(prev_node_id) = self.prev_node_id {
					if prev_node_id == node_id {
						return None;
					}
				}
				let data = &mut lattice.data[node_id as usize].data;
				self.prev_node_id = Some(node_id);
				Some(data)
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn smallest_possible_grid() {
		let _grid: SeamLattice<u32> = SeamLattice::new(1, 1);
		assert!(true, "Grid constructed");
	}

	#[test]
	fn smallest_grid_is_self_referring() {
		let grid: SeamLattice<u32> = SeamLattice::new(1, 1);
		let root = grid.root;
		for i in UP..=DN {
			for j in LF..=RT {
				if i == 0 && j == 0 {
					continue;
				}
				assert_eq!(
					grid.transit(root, i, j),
					root,
					"One node transition was not self-referring"
				)
			}
		}
	}

	macro_rules! test_dm {
		($grid:expr, $root:expr, $i:ident, $j:ident) => {
			assert_eq!(
				$grid.transit_by_direction($root, dm!($i, $j)),
				$root,
				"One node transition was not self-referring in macro"
			);
		};
	}

	#[test]
	fn smallest_grid_is_statically_self_referring() {
		let grid: SeamLattice<u32> = SeamLattice::new(1, 1);
		let root = grid.root;
		test_dm!(grid, root, LF, UP);
		test_dm!(grid, root, SM, UP);
		test_dm!(grid, root, RT, UP);
		test_dm!(grid, root, LF, SM);
		test_dm!(grid, root, RT, SM);
		test_dm!(grid, root, LF, DN);
		test_dm!(grid, root, SM, DN);
		test_dm!(grid, root, LF, DN);
	}

	#[test]
	fn triple_grid_is_self_referring() {
		let grid: SeamLattice<u32> =
			SeamLattice::create_from_grid(3, 3, &vec![10, 11, 12, 13, 14, 15, 16, 17, 18]);
		let center = grid.transit(grid.root, DN, RT);
		assert_eq!(grid[center], 14);

		assert_eq!(grid[grid.transit(center, LF, UP)], 10);
		assert_eq!(grid[grid.transit(center, SM, UP)], 11);
		assert_eq!(grid[grid.transit(center, RT, UP)], 12);
		assert_eq!(grid[grid.transit(center, LF, SM)], 13);
		assert_eq!(grid[grid.transit(center, RT, SM)], 15);
		assert_eq!(grid[grid.transit(center, LF, DN)], 16);
		assert_eq!(grid[grid.transit(center, SM, DN)], 17);
		assert_eq!(grid[grid.transit(center, RT, DN)], 18);
	}

	struct Summer(NodeId, i32, i32);
	impl WalkStep<u32> for Summer {
		fn step(&mut self, lattice: &SeamLattice<u32>) -> Option<NodeId> {
			let cur = self.0;
			self.0 = lattice.transit(self.0, self.1, self.2);
			Some(cur)
		}
	}

	fn visit(walker: &mut Walker<u32>, lattice: &SeamLattice<u32>) -> u32 {
		let mut total = 0;
		while let Some(v) = walker.next(lattice) {
			total += *v;
		}
		total
	}

	fn build_walker(node_id: NodeId, x: i32, y: i32) -> Walker<u32> {
		Walker::new(Box::new(Summer(node_id, x, y)))
	}

	#[test]
	fn visit_threeby_grid() {
		let grid: SeamLattice<u32> =
			SeamLattice::create_from_grid(3, 3, &vec![10, 11, 12, 13, 14, 15, 16, 17, 18]);

		let mut walker = build_walker(0, RT, SM);
		assert_eq!(visit(&mut walker, &grid), 33);

		let mut walker = build_walker(3, RT, SM);
		assert_eq!(visit(&mut walker, &grid), 42);

		let mut walker = build_walker(6, RT, SM);
		assert_eq!(visit(&mut walker, &grid), 51);

		let mut walker = build_walker(0, RT, DN);
		assert_eq!(visit(&mut walker, &grid), 42);

		let mut walker = build_walker(2, LF, DN);
		assert_eq!(visit(&mut walker, &grid), 42);
	}

	struct GridSummer(NodeId, NodeId, bool);

	impl GridSummer {
		fn new(node_id: NodeId) -> GridSummer {
			GridSummer(node_id, node_id, false)
		}
	}

	// While traversing in one dimension, the sentinel is false UNTIL
	// the pointer to the last object in the row has been retrieved
	// for return.  At the next phase, the sentinel is checked and
	// if

	impl WalkStep<u32> for GridSummer {
		fn step(&mut self, lattice: &SeamLattice<u32>) -> Option<NodeId> {
			let cur = if self.2 {
				let nextrow = lattice.transit(self.1, SM, DN);
				if nextrow == self.1 {
					return None;
				}
				let cur = nextrow;
				self.1 = cur;
				self.2 = false;
				cur
			} else {
				self.0
			};

			self.0 = lattice.transit(cur, RT, SM);
			if cur == self.0 {
				self.2 = true;
			}
			Some(cur)
		}
	}

	#[test]
	fn visit_whole_grid() {
		let grid: SeamLattice<u32> =
			SeamLattice::create_from_grid(3, 3, &vec![10, 11, 12, 13, 14, 15, 16, 17, 18]);
		let mut walker = Walker::new(Box::new(GridSummer::new(0)));
		assert_eq!(visit(&mut walker, &grid), 126);
	}

	#[test]
	fn modify_whole_grid() {
		let mut grid: SeamLattice<u32> =
			SeamLattice::create_from_grid(3, 3, &vec![10, 11, 12, 13, 14, 15, 16, 17, 18]);

		let mut walker = Walker::new(Box::new(GridSummer::new(0)));
		while let Some(v) = walker.next_mut(&mut grid) {
			*v = *v * 10;
		}

		let mut walker = Walker::new(Box::new(GridSummer::new(0)));
		assert_eq!(visit(&mut walker, &grid), 1260);
	}
}
