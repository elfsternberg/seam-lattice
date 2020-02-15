// #![deny(missing_docs)]
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! SeamLattice
//!
//! The SeamLattice represents a two-dimensional grid as a graph, each
//! point on the grid connected to its eight cardinal neighbors by an
//! edge, the function for which is
//!      `(NodeID, CardinalDirection) -> NodeId`.

//! With this, it's possible to navigate about a grid simply by
//! providing a NodeId and a step.  Several "iterators" are provided
//! that will provide a sequence of node addresses, either scanning
//! left-to-right, top-to-bottom, or any combination of the two.
//!
//! By providing the SeamLattice as a standalone memory object with no
//! relationship to the grids it represents, it's hoped that
//! *traversal*, *analysis*, and *mutation* can all be broken into
//! separate components, and that traversal and analysis can be
//! conducted independently and in parallel.

#[allow(unused_imports)]
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

/// Go up! These constants are used to decide cardinal points for
/// transitions.
pub const UP: i8 = -1;
/// Go down!
pub const DN: i8 = 1;
/// Go left!
pub const LF: i8 = -1;
/// Go right!
pub const RT: i8 = 1;
/// Don't go anywhere!
pub const SM: i8 = 0;

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
pub fn dm(y: i8, x: i8) -> u32 {
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

#[derive(Debug, Clone)]
/// Abstract Node in the Lattice; knows only what data you give it,
/// plus information about the neighbors that should really be
/// private.
pub struct Node([u32; 8]);

type NodeId = u32;

//  _         _   _   _
// | |   __ _| |_| |_(_)__ ___
// | |__/ _` |  _|  _| / _/ -_)
// |____\__,_|\__|\__|_\__\___|
//

#[derive(Copy, Clone, PartialEq)]
enum Direction {
	Upward,
	Downward,
	Leftward,
	Rightward,
}

/// The base class for this library.  
pub struct SeamLattice {
	width: u32,
	height: u32,
	current_width: u32,
	current_height: u32,
	root: NodeId,
	nodes: Vec<Node>,
}

// Private, obviously.  Assumes the vector will be a 1:1
// representation of the source data, such that an image could be
// reconstructed when finished.
fn calculate_neighbors(point: u32, width: u32, height: u32) -> [u32; 8] {
	let h = point / width;
	let w = point % width;
	let mut neighbors: [u32; 8] = [0; 8];
	for hstep in UP..=DN {
		for wstep in LF..=RT {
			if hstep == 0 && wstep == 0 {
				continue;
			}
			let node_ptr = dm(wstep, hstep);
			neighbors[node_ptr as usize] = {
				let hpoint = (h as i32) + (hstep as i32);
				let wpoint = (w as i32) + (wstep as i32);
				if hpoint < 0 || hpoint >= height as i32 || wpoint < 0 || wpoint >= width as i32 {
					point as u32
				} else {
					width * (hpoint as u32) + (wpoint as u32)
				}
			};
		}
	}
	neighbors
}

impl SeamLattice {
	/// Build a lattice from a source vector.  As this assumes a
	/// two-dimensional space, the width and height of the source must
	/// be included.
	pub fn new(width: u32, height: u32) -> Self {
		let nodes = (0..width * height)
			.map(|p| Node(calculate_neighbors(p, width, height)))
			.collect();
		SeamLattice {
			width,
			height,
			current_width: width,
			current_height: height,
			root: 0,
			nodes,
		}
	}

	/// Returns the address of a connected node using a cardinal
	/// direction.
	pub fn transit_by_direction(&self, node: u32, direction: u32) -> NodeId {
		self.nodes[node as usize].0[direction as usize]
	}

	/// Returns the address of a connected node by specifying the vertical
	/// and horizontal directions.
	pub fn transit(&self, node: u32, x: i8, y: i8) -> NodeId {
		self.transit_by_direction(node, dm(x, y))
	}

	/// Returns an iterator over the data.
	pub fn data(&self) -> SeamLatticeScannerIterator {
		SeamLatticeScannerIterator::new(self)
	}

	/// Returns an iterator that, given a starting node, traverses
	/// rightward, returning the coordinate for each node in a row.
	pub fn row(&self, start: NodeId) -> SeamLatticeLineIterator {
		SeamLatticeLineIterator::new(self, start, dm!(RT, SM))
	}

	/// Returns an iterator that, given a starting node, traverses
	/// downward, returning the coordinate for each node in a column.
	pub fn col(&self, start: NodeId) -> SeamLatticeLineIterator {
		SeamLatticeLineIterator::new(self, start, dm!(SM, DN))
	}

	pub fn validate_seam(&self, seam: &[u32]) -> bool {
		let sl = seam.len() as u32;
		// Trivially true.
		if sl < 2 {
			return true;
		}

		// Seam has to follow one of these, either top-bottom or left-right
		if sl != self.current_width && sl != self.current_height {
			println!("Seam doesn't fit this grid");
			return false;
		}

		fn is_border(seam: &[NodeId], nodes: &Vec<Node>, point: usize) -> bool {
			let pos = seam[point] as usize;
			let node = &nodes[pos];
			let selfrefs = (0..8).fold(0, |a, c| if node.0[c] == (pos as u32) { a + 1 } else { a });
			(selfrefs >= 3)
		}

		// The first or last node is not a border node.
		if !(is_border(seam, &self.nodes, 0) && is_border(seam, &self.nodes, seam.len() - 1)) {
			println!("Seam endpoints do not seem to be on a border");
			return false;
		}

		// The seam nodes are actually parts of a seam:
		let mut news: Vec<[u32; 3]> = vec![
			[dm!(LF, UP), dm!(SM, UP), dm!(RT, UP)],
			[dm!(LF, DN), dm!(SM, DN), dm!(RT, DN)],
			[dm!(LF, UP), dm!(LF, SM), dm!(LF, DN)],
			[dm!(RT, UP), dm!(RT, SM), dm!(RT, DN)],
		];

		for seam_pair in seam.windows(2) {
			let current_node = &self.nodes[seam_pair[0] as usize];

			// Find the cardinal direction of the next node from the
			// current node.
			let p = (0..8).find(|a| current_node.0[*a] == seam_pair[1]);

			// If we can't find one, then the next node is not a
			// neighboring node!
			if p.is_none() {
				println!(
					"Node {} is not a neighbor of {}",
					seam_pair[0], seam_pair[1]
				);
				return false;
			}

			// From the collection of possible directions, filter out
			// those that have the direction requested.
			let p = p.unwrap() as u32;
			news = news
				.into_iter()
				.filter(|&d| d.iter().find(|&c| *c == p).is_some())
				.collect();

			println!("{:?}", news);

			// If the news length drops to zero, we've encountered a
			// direction that has already been filtered out, in which
			// case the path is going in an invalid direction for a
			// valid seam.
			if news.len() == 0 {
				println!("Seam seems to wander in the wrong direction.");
				// Wandered in the wrong direction.
				return false;
			}
		}
		println!("");
		true
	}
}

impl std::fmt::Debug for SeamLattice {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		writeln!(
			f,
			"SeamLattice {{ width: {}, height: {}, root: {}",
			self.width, self.height, self.root
		)
		.unwrap();
		for i in &self.nodes {
			writeln!(f, "    {:?}", i).unwrap();
		}
		writeln!(f, "}}")
	}
}

//  ___ _                _
// |_ _| |_ ___ _ _ __ _| |_ ___ _ _ ___
//  | ||  _/ -_) '_/ _` |  _/ _ \ '_(_-<
// |___|\__\___|_| \__,_|\__\___/_| /__/
//

// There are several kinds of "iterators:" the first gives a list of
// all the contents of a single row or column, the other a complete
// scan of the grid, always starting at the root and traversing either
// horizontally first, then vertically, visiting every row in order,
// or vice-versa, visiting every column.

//    ______
//   / __/ /____ ___
//  _\ \/ __/ -_) _ \
// /___/\__/\__/ .__/
//            /_/

/// This trait takes a lattice and returns a new NodeId, indicating
/// where the next step should be.
pub trait Walkstep {
	/// Given a lattice, return the address found by taking a step.
	fn next(&mut self, lattice: &SeamLattice) -> Option<NodeId>;
}

//  ___
// / __| __ __ _ _ _  _ _  ___ _ _
// \__ \/ _/ _` | ' \| ' \/ -_) '_|
// |___/\__\__,_|_||_|_||_\___|_|
//

pub struct OneLineScanner {
	direction: u32,
	node_id: NodeId,
	halt: bool,
}

impl OneLineScanner {
	pub fn new(node_id: NodeId, direction: u32) -> Self {
		OneLineScanner {
			direction,
			node_id,
			halt: false,
		}
	}

	pub fn horizontal(start: NodeId) -> Self {
		Self::new(start, dm!(RT, SM))
	}

	pub fn vertical(start: NodeId) -> Self {
		Self::new(start, dm!(SM, DN))
	}
}

impl Walkstep for OneLineScanner {
	fn next(&mut self, lattice: &SeamLattice) -> Option<NodeId> {
		let next_node_id = lattice.transit_by_direction(self.node_id, self.direction);
		if self.halt {
			return None;
		}
		if next_node_id == self.node_id {
			self.halt = true;
		}
		let node_id = self.node_id;
		self.node_id = next_node_id;
		Some(node_id)
	}
}

pub struct Scanner {
	first: OneLineScanner,
	second: OneLineScanner,
}

impl Scanner {
	pub fn horizontal_first(lattice: &SeamLattice) -> Self {
		let mut scanner = Scanner {
			first: OneLineScanner::horizontal(lattice.root),
			second: OneLineScanner::vertical(lattice.root),
		};
		scanner.second.next(&lattice);
		scanner
	}

	pub fn vertical_first(lattice: &SeamLattice) -> Self {
		let mut scanner = Scanner {
			first: OneLineScanner::vertical(lattice.root),
			second: OneLineScanner::horizontal(lattice.root),
		};
		scanner.second.next(&lattice);
		scanner
	}
}

impl Walkstep for Scanner {
	fn next(&mut self, lattice: &SeamLattice) -> Option<NodeId> {
		match self.first.next(lattice) {
			None => {
				let next_line_node_id = self.second.next(&lattice);
				match next_line_node_id {
					None => None,
					Some(node_id) => {
						let direction = self.first.direction;
						self.first = OneLineScanner {
							direction,
							node_id,
							halt: false,
						};
						self.next(lattice)
					}
				}
			}
			Some(node_id) => Some(node_id),
		}
	}
}

//  ___       _          ___ _                _
// |   \ __ _| |_ __ _  |_ _| |_ ___ _ _ __ _| |_ ___ _ _
// | |) / _` |  _/ _` |  | ||  _/ -_) '_/ _` |  _/ _ \ '_|
// |___/\__,_|\__\__,_| |___|\__\___|_| \__,_|\__\___/_|
//

/// A very simple iterator, that extracts the data in the
/// expected order for recovering an image.
pub struct SeamLatticeScannerIterator<'a> {
	lattice: &'a SeamLattice,
	scanner: Scanner,
}

impl<'a> SeamLatticeScannerIterator<'a> {
	/// Construct a new, simple iterator for retrieving copies of the
	/// data objects used by the lattice.
	pub fn new(lattice: &'a SeamLattice) -> Self {
		SeamLatticeScannerIterator {
			lattice,
			scanner: Scanner::horizontal_first(lattice),
		}
	}
}

impl<'a> Iterator for SeamLatticeScannerIterator<'a> {
	type Item = NodeId;
	fn next(&mut self) -> Option<NodeId> {
		self.scanner.next(self.lattice)
	}
}

/// A very simple iterator that scans either a horizontal or vertical
/// line.
pub struct SeamLatticeLineIterator<'a> {
	lattice: &'a SeamLattice,
	scanner: OneLineScanner,
}

impl<'a> SeamLatticeLineIterator<'a> {
	pub fn new(lattice: &'a SeamLattice, start: NodeId, direction: u32) -> Self {
		SeamLatticeLineIterator {
			lattice,
			scanner: OneLineScanner::new(start, direction),
		}
	}
}

impl<'a> Iterator for SeamLatticeLineIterator<'a> {
	type Item = NodeId;
	fn next(&mut self) -> Option<NodeId> {
		self.scanner.next(self.lattice)
	}
}

//  __  __      _        _
// |  \/  |_  _| |_ __ _| |_ ___ _ _ ___
// | |\/| | || |  _/ _` |  _/ _ \ '_(_-<
// |_|  |_|\_,_|\__\__,_|\__\___/_| /__/
//

// There is only one kind of a mutator, and it removes a seam.  It
// does this by taking a vec of addresses for the seam, and either
// "shifting everything to the right leftward one", or by "shifting
// everything underneath upward one," depending on the orientation of
// the operation.

//  _____       _
// |_   _|__ __| |_ ___
//   | |/ -_|_-<  _(_-<
//   |_|\___/__/\__/__/
//

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn smallest_possible_grid() {
		let _grid = SeamLattice::new(1, 1);
		assert!(true, "Grid constructed");
	}

	#[test]
	fn smallest_grid_is_self_referring() {
		let sample = vec![0];
		let grid = SeamLattice::new(1, 1);
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
		let grid = SeamLattice::new(1, 1);
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
		let grid = SeamLattice::new(3, 3);
		let center = grid.transit(grid.root, DN, RT);
		assert_eq!(center, 4);
		assert_eq!(grid.transit(center, LF, UP), 0);
		assert_eq!(grid.transit(center, SM, UP), 1);
		assert_eq!(grid.transit(center, RT, UP), 2);
		assert_eq!(grid.transit(center, LF, SM), 3);
		assert_eq!(grid.transit(center, RT, SM), 5);
		assert_eq!(grid.transit(center, LF, DN), 6);
		assert_eq!(grid.transit(center, SM, DN), 7);
		assert_eq!(grid.transit(center, RT, DN), 8);
	}

	#[test]
	fn visit_three_by_grid() {
		let sample = vec![10, 11, 12, 13, 14, 15, 16, 17, 18];
		let expected = sample.iter().sum();
		let grid = SeamLattice::new(3, 3);
		let mut scanner = OneLineScanner::horizontal(grid.root);
		let mut tot = 0;
		while let Some(pos) = scanner.next(&grid) {
			tot += sample[pos as usize];
		}
		assert_eq!(tot, 33);

		let mut scanner = OneLineScanner::vertical(grid.root);
		let mut tot = 0;
		while let Some(pos) = scanner.next(&grid) {
			tot += sample[pos as usize];
		}
		assert_eq!(tot, 39);

		let mut scanner = Scanner::horizontal_first(&grid);
		let mut tot = 0;
		while let Some(pos) = scanner.next(&grid) {
			tot += sample[pos as usize];
		}
		assert_eq!(tot, expected);

		let mut scanner = Scanner::vertical_first(&grid);
		let mut tot = 0;
		while let Some(pos) = scanner.next(&grid) {
			tot += sample[pos as usize];
		}
		assert_eq!(tot, expected);
	}

	#[test]
	fn iterator_three_by_grid() {
		let sample = vec![10, 11, 12, 13, 14, 15, 16, 17, 18];
		let expected: u32 = sample.iter().sum();
		let grid = SeamLattice::new(3, 3);
		let scan = SeamLatticeScannerIterator::new(&grid);
		let tot: u32 = scan.map(|p| sample[p as usize]).sum();
		assert_eq!(tot, expected);
	}

	#[test]
	fn validate_empty_seam() {
		let sample: Vec<u32> = vec![];
		let grid = SeamLattice::new(0, 0);
		assert!(grid.validate_seam(&[]));
	}

	#[test]
	fn validate_single_node_seam() {
		let sample: Vec<u32> = vec![4];
		let grid = SeamLattice::new(1, 1);
		assert!(grid.validate_seam(&[0]));
	}

	#[test]
	fn validate_dual_node_single_seam() {
		let sample: Vec<u32> = vec![4, 5];
		let grid = SeamLattice::new(2, 1);
		assert!(grid.validate_seam(&[1]));
	}

	#[test]
	fn validate_dual_node_double_seam() {
		let sample: Vec<u32> = vec![4, 5];
		let grid = SeamLattice::new(2, 1);
		assert!(grid.validate_seam(&[1, 0]));
	}

	#[test]
	fn validate_threeby_seams() {
		let grid = SeamLattice::new(3, 3);
		assert!(grid.validate_seam(&[0, 1, 2]));
		assert!(grid.validate_seam(&[3, 4, 5]));
		assert!(grid.validate_seam(&[6, 7, 8]));
		assert!(grid.validate_seam(&[1, 4, 7]));
		assert!(grid.validate_seam(&[2, 5, 8]));
		assert!(grid.validate_seam(&[0, 4, 8]));
		assert!(grid.validate_seam(&[6, 4, 2]));
		assert!(
			!grid.validate_seam(&[3, 4, 1]),
			"Grid appears to go in the wrong direction!"
		);
		assert!(
			!grid.validate_seam(&[0, 1, 6]),
			"Grid validates a disconnected seam"
		);
	}

	/*
	#[test]
	fn remove_center_seam() {
		let sample: Vec<u32> = vec![10, 11, 12, 13, 14, 15, 16, 17, 18];
		let expected: Vec<u32> = vec![10, 11, 12, 16, 17, 18];
		let grid = SeamLattice::new(3, 3);
		let root = grid.transit(grid.root, SM, DN);
		assert_eq!(root, 3);
		let nodes: Vec<u32> = grid.row(root).collect();
		assert_eq!(nodes, vec![3, 4, 5]);
		grid.remove_seam(nodes);
		let result: Vec<u32> = grid.data().collect();
		assert_eq!(result, expected);
	}
	*/
}
