use std::ops::{Index, IndexMut};

// Conventions!
//
// We always, *ALWAYS*, refer to width, height, in that order.  The
// position of a node on a _grid_ is therefore always `y * width + x`,
// that is, the number of rows DOWN is calculated as an offset
// multiple of the width, followed by the offset into the row to find
// the node.
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

macro_rules! cq {
	($condition: expr, $_true: expr, $_false: expr) => {
		if $condition {
			$_true
		} else {
			$_false
			}
	};
}

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
pub struct Point<P: Default + Copy> {
	pub neighbors: [u32; 8],
	pub data: P,
}

type Root = u32;

#[derive(Debug)]
pub struct SeamLattice<P: Default + Copy> {
	pub width: u32,
	pub height: u32,
	pub root: Root,
	data: Vec<Point<P>>,
}

fn initialize_lattice<P: Default + Copy>(width: u32, height: u32, data: &mut Vec<Point<P>>) {
	let mw = width - 1;
	let mh = height - 1;

	for h in 0..height {
		for w in 0..width {
			for ny in UP..=DN {
				for nx in LF..=RT {
					if ny == 0 && nx == 0 {
						continue;
					}
					let pos = (h as usize) * (width as usize) + (w as usize);
					let node_ptr = dm(nx, ny);
					data[pos].neighbors[node_ptr as usize] = {
						let tx = (h as i32) + ny;
						let ty = (w as i32) + nx;
						let ntx = cq!(tx < 0, 0, cq!(tx > mw as i32, mw, tx as u32));
						let nty = cq!(ty < 0, 0, cq!(ty > mh as i32, mh, ty as u32));
						nty * width + ntx
					};
				}
			}
		}
	}
}

// Brainstorming: the visitor "needs" to visit any number of points on
// the grid.  So it either knows its root-- or can retrieve it.
// Visitors need to be clone-able, or at least reproducible from a
// factory for the purpose of aggregating multi-core soltions.  So,
// the visitor visits a node... then what?  Somehow signals that it
// needs the next node in a given direction, or that it's done.

// Even worse, imagine this: the COLUMN visitor is visiting rows, but
// for each COLUMN it then produces a new ROW of data, which then has
// to be written back to the core data structure in order to record
// the unit of work.  So we have a dance, and at its heart is a
// mutation, and that's.. difficult.

impl<P: Default + Copy> SeamLattice<P> {
	pub fn new(width: u32, height: u32) -> Self {
		let mut data = vec![Point::<P>::default(); width as usize * height as usize];
		initialize_lattice(width, height, &mut data);
		SeamLattice {
			width,
			height,
			root: 0,
			data,
		}
	}

	pub fn create_from_grid(width: u32, height: u32, source: &Vec<P>) -> Self {
		let mut data = vec![Point::<P>::default(); width as usize * height as usize];
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

	pub fn transit_by_direction(&self, node: u32, direction: u32) -> u32 {
		self.data[node as usize].neighbors[direction as usize]
	}

	pub fn transit(&self, node: u32, x: i32, y: i32) -> u32 {
		self.transit_by_direction(node, dm(x, y))
	}
}

impl<P: Default + Copy> Index<u32> for SeamLattice<P> {
	type Output = P;

	/// A convenience addressing mode for getting values.
	fn index(&self, p: u32) -> &P {
		&self.data[p as usize].data
	}
}

impl<P: Default + Copy> IndexMut<u32> for SeamLattice<P> {
	/// A convenience addressing mode for setting values.
	fn index_mut(&mut self, p: u32) -> &mut P {
		&mut self.data[p as usize].data
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

		assert_eq!(grid[grid.transit(center, UP, LF)], 10);
		assert_eq!(grid[grid.transit(center, UP, SM)], 11);
		assert_eq!(grid[grid.transit(center, UP, RT)], 12);
		assert_eq!(grid[grid.transit(center, SM, LF)], 13);
		assert_eq!(grid[grid.transit(center, SM, RT)], 15);
		assert_eq!(grid[grid.transit(center, DN, LF)], 16);
		assert_eq!(grid[grid.transit(center, DN, SM)], 17);
		assert_eq!(grid[grid.transit(center, DN, RT)], 18);
	}
}
