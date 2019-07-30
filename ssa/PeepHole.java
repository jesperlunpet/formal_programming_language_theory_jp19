// The name of a package is "coins.ssa"
package coins.ssa;

import coins.backend.LocalTransformer;
import coins.backend.Data;
import coins.backend.Type;
import coins.backend.Function;
import coins.backend.cfg.BasicBlk;
import coins.backend.util.BiLink;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirBinOp;
import coins.backend.lir.LirIconst;
import coins.backend.lir.LirFconst;
import coins.backend.lir.LirSymRef;
import coins.backend.lir.LirNode;
import coins.backend.util.ImList;
import coins.backend.cfg.FlowGraph;

// Import coins.backend.Op, if you would like to refer kinds of operators.
import coins.backend.Op;

import java.util.HashMap;
import java.util.Map;

// Implement LocalTransformer
public class PeepHole implements LocalTransformer {

	private SsaEnvironment env;
	private SsaSymTab sstab;
	// Map with all variables
	private Map map = new HashMap<LirSymRef, Object>();

	public PeepHole(SsaEnvironment e, SsaSymTab tab) {
		env = e;
		sstab = tab;
	}

	public String name() { return "PeepHole"; }
	public String subject() {
		return "Simple optimizer using peephole approach";
	}

	public boolean doIt(Data data, ImList args) { return true; }

	public boolean doIt(Function function,ImList args) {
		// making a control graph.
		FlowGraph flow = function.flowGraph();

		for(BiLink bbl = flow.basicBlkList.first(); !bbl.atEnd(); bbl=bbl.next()) {
			BasicBlk bb=(BasicBlk)bbl.elem();
			System.out.println("The Block:");
			System.out.println(bb.instrList().toString());
			System.out.println("Every Peephole optimization:");
			// Two continuous statements, "prevNode" and "node", are considered as a peephole,
			// where prevNode records an immediately previous node of the node
			BiLink prevNodel = null;

			// Map to save all constant values

			for(BiLink nodel=bb.instrList().first();!nodel.atEnd();
				prevNodel = nodel, nodel = nodel.next()) {
				if (prevNodel != null) {
					LirNode node = (LirNode)nodel.elem();
					LirNode prevNode = (LirNode)prevNodel.elem();
					// If the peephole matches a pattern:
					// (SET (MEM x) (REG r)); (SET (REG r') (MEM x)), where
					// a subexpression (MEM x) of prevNode has to correspond to one of the node,
					// it can be transformed as follows:
					// (SET (MEM x) (REG r)); (SET (REG r') (REG r))
					if (node.opCode == Op.SET && prevNode.opCode == Op.SET &&
							prevNode.kid(0).opCode == Op.MEM &&
							(prevNode.kid(1).opCode == Op.REG ||
									prevNode.kid(1).opCode == Op.INTCONST ||
									prevNode.kid(1).opCode == Op.FLOATCONST) &&
							node.kid(0).opCode == Op.REG && node.kid(1).opCode == Op.MEM &&
							node.kid(1).equals(prevNode.kid(0))) {

						// Printing a statement before transformation for confirmation
						 System.out.println(node.toString()+" is ");

						// Transformation of node.
						// The right-hand side is replaced with the left-hand side of prevNode.
						// LirNode has a tree structure. ith child of a node can be extracted through
						// node.kid(i), where i starts from 0.
						// If you would like to replace ith child of a node with node',
						// you can take advantage of node.setKid(i, node').
						// At this time, you may not directly use a part of other LirNode as node'.
						// Namely, node' has to be one copied from the part through makeCopy(env.lir).
						node.setKid(1, prevNode.kid(1).makeCopy(env.lir));

						// Printing a statement after transformation for confirmation
						 System.out.println("\treplaced with " + node.toString());
					}

					// Combine operation with CONVSF and constant values
					if (node.opCode == Op.SET && node.kid(1).opCode == Op.CONVSF && node.kid(1).kid(0).opCode == Op.INTCONST) {
						System.out.println("---Combine Operation---");
						// Always followed by another node
						LirNode next = (LirNode) nodel.next().elem();
						System.out.println(node.toString()+" and ");
						System.out.println(next.toString()+" is ");
						if (next.kid(1).kid(0) == node.kid(0)) {
							next.kid(1).setKid(0, new LirFconst(node.kid(1).kid(0).id, Op.FLOATCONST, (double)((LirIconst)node.kid(1).kid(0)).value, node.kid(1).kid(0).opt));
						} else if (next.kid(1).kid(1) == node.kid(0))
							next.kid(1).setKid(1, new LirFconst(node.kid(1).kid(0).id, Op.FLOATCONST, (double)((LirIconst)node.kid(1).kid(0)).value, node.kid(1).kid(0).opt));
						System.out.println("\treplaced with " + next.toString());
					}

					// If REG already has a constant value, change it.
					if (node.opCode == Op.SET && node.kid(1).nKids() == 2) {
						if (node.kid(1).kid(0).opCode == Op.REG && map.containsKey(node.kid(1).kid(0))) {
							if (map.get(node.kid(1).kid(0)) instanceof Long) {
								node.kid(1).setKid(0, new LirIconst(node.kid(1).kid(0).id, Op.INTCONST, (Long)map.get(node.kid(1).kid(0)), node.kid(1).kid(0).opt));
							} else {
								node.kid(1).setKid(0, new LirFconst(node.kid(1).kid(0).id, Op.FLOATCONST, (Double)map.get(node.kid(1).kid(0)), node.kid(1).kid(0).opt));
							}
						}
						if (node.kid(1).kid(1).opCode == Op.REG && map.containsKey(node.kid(1).kid(1))) {
							if (map.get(node.kid(1).kid(1)) instanceof Long) {
								node.kid(1).setKid(1, new LirIconst(node.kid(1).kid(1).id, Op.INTCONST, (Long)map.get(node.kid(1).kid(1)), node.kid(1).kid(1).opt));
							} else {
								node.kid(1).setKid(1, new LirFconst(node.kid(1).kid(1).id, Op.FLOATCONST, (Double)map.get(node.kid(1).kid(1)), node.kid(1).kid(1).opt));
							}

						}
					}

					// Constant folding
					if (node.opCode == Op.SET && (node.kid(1).opCode == Op.ADD || node.kid(1).opCode == Op.MUL || node.kid(1).opCode == Op.SUB ||
							node.kid(1).opCode == Op.DIVS || node.kid(1).opCode == Op.DIVU || node.kid(1).opCode == Op.MODU || node.kid(1).opCode == Op.MODS) &&
							((node.kid(1).kid(0).opCode == Op.INTCONST || node.kid(1).kid(0).opCode == Op.FLOATCONST) && (node.kid(1).kid(1).opCode == Op.INTCONST || node.kid(1).kid(1).opCode == Op.FLOATCONST))) {
						System.out.println("---Constant Folding---");
						System.out.println(node.toString()+" is ");
						getValue(node);
						System.out.println("\treplaced with " + node.toString());
					// Strength reduction (one input must be an unknown variable)
					}
					if (node.opCode == Op.SET && (node.kid(1).opCode == Op.MUL || node.kid(1).opCode == Op.DIVS || node.kid(1).opCode == Op.DIVU) &&
							(node.kid(1).kid(0).opCode == Op.INTCONST || node.kid(1).kid(1).opCode == Op.INTCONST)) {
						// Needs to be a copy or a global value is changed.
						LirNode strengthReducedNode = strengthReduction(node.makeCopy(env.lir));
						if (!strengthReducedNode.equals(node)) {
							System.out.println("---Strength Reduction---");
							System.out.println(node.toString()+" is ");
							System.out.println("\treplaced with " + strengthReducedNode.toString());
						}
					}

					if (node.opCode == Op.SET) {
						if (node.kid(1).opCode == Op.INTCONST) {
							// The REG must have a constant value.
							map.put(node.kid(0), ((LirIconst) node.kid(1)).value);
						} else if (node.kid(1).opCode == Op.FLOATCONST) {
							map.put(node.kid(0), ((LirFconst) node.kid(1)).value);
						} else {
							// We no longer know the value of REG for certain.
							map.remove(node.kid(0));
						}
					}
				}
			}
		}
		// Keeping track of variables is much harder and out of scope for constant folding, therefore clear the map for every map.
		map.clear();

		// If you have modified a control flow graph, you have to touch it.
		flow.touch();

		// The last of "doIt" returns true.
		return(true);
	}
	private long evaluate(long first, long second, int opCode) {
		switch (opCode) {
			case Op.MUL:
				return first * second;
			case Op.ADD:
				return first + second;
			case Op.SUB:
				return first - second;
			case Op.DIVU:
				// Unsigned and signed integers are treated the same here
			case Op.DIVS:
				return first / second;
			case Op.MODU:
				// Unsigned and signed integers are treated the same here
			case Op.MODS:
				return first % second;
			default:
				throw new Error("Reached unexpected case in evaluating");
		}
	}
	private double evaluate(long first, double second, int opCode) {
		switch (opCode) {
			case Op.MUL:
				return first * second;
			case Op.ADD:
				return first + second;
			case Op.SUB:
				return first - second;
			case Op.DIVU:
				// Unsigned and signed integers are treated the same here
			case Op.DIVS:
				return first / second;
			case Op.MODU:
				// Unsigned and signed integers are treated the same here
			case Op.MODS:
				return first % second;
			default:
				throw new Error("Reached unexpected case in evaluating");
		}
	}
	private double evaluate(double first, long second, int opCode) {
		switch (opCode) {
			case Op.MUL:
				return first * second;
			case Op.ADD:
				return first + second;
			case Op.SUB:
				return first - second;
			case Op.DIVU:
				// Unsigned and signed integers are treated the same here
			case Op.DIVS:
				return first / second;
			case Op.MODU:
				// Unsigned and signed integers are treated the same here
			case Op.MODS:
				return first % second;
			default:
				throw new Error("Reached unexpected case in evaluating");
		}
	}
	private double evaluate(double first, double second, int opCode) {
		switch (opCode) {
			case Op.MUL:
				return first * second;
			case Op.ADD:
				return first + second;
			case Op.SUB:
				return first - second;
			case Op.DIVU:
				// Unsigned and signed integers are treated the same here
			case Op.DIVS:
				return first / second;
			case Op.MODU:
				// Unsigned and signed integers are treated the same here
			case Op.MODS:
				return first % second;
			default:
				throw new Error("Reached unexpected case in evaluating");
		}
	}

	private void getValue(LirNode node) {
		if (node.kid(1).kid(0).opCode == Op.INTCONST && node.kid(1).kid(1).opCode == Op.INTCONST) {
			node.setKid(1, new LirIconst(node.kid(1).id, node.kid(1).type, evaluate(((LirIconst)node.kid(1).kid(0)).value, ((LirIconst)node.kid(1).kid(1)).value, node.kid(1).opCode), node.kid(1).opt));
		} else if (node.kid(1).kid(0).opCode == Op.INTCONST && node.kid(1).kid(1).opCode == Op.FLOATCONST) {
			node.setKid(1, new LirFconst(node.kid(1).id, node.kid(1).type, evaluate(((LirIconst)node.kid(1).kid(0)).value, ((LirFconst)node.kid(1).kid(1)).value, node.kid(1).opCode), node.kid(1).opt));
		} else if (node.kid(1).kid(0).opCode == Op.FLOATCONST && node.kid(1).kid(1).opCode == Op.INTCONST) {
			node.setKid(1, new LirFconst(node.kid(1).id, node.kid(1).type, evaluate(((LirFconst)node.kid(1).kid(0)).value, ((LirIconst)node.kid(1).kid(1)).value, node.kid(1).opCode), node.kid(1).opt));
		} else if (node.kid(1).kid(0).opCode == Op.FLOATCONST && node.kid(1).kid(1).opCode == Op.FLOATCONST) {
			node.setKid(1, new LirFconst(node.kid(1).id, node.kid(1).type, evaluate(((LirFconst)node.kid(1).kid(0)).value, ((LirFconst)node.kid(1).kid(1)).value, node.kid(1).opCode), node.kid(1).opt));
		} else {
			throw new Error("Expected either float or int input");
		}
	}

	private LirNode strengthReduction(LirNode node) {
		switch (node.kid(1).opCode) {
			case Op.MUL:
				if (node.kid(1).kid(0).opCode == Op.REG && logicalShift(((LirIconst) node.kid(1).kid(1)).value) != 0) {
					node.setKid(1, new LirBinOp(node.kid(1).id, Op.LSHS, node.kid(1).type, node.kid(1).kid(0),
							new LirIconst(node.kid(1).kid(1).id, node.kid(1).kid(1).type, logicalShift(((LirIconst) node.kid(1).kid(1)).value), node.kid(1).kid(1).opt), node.kid(1).opt));
				} else if (node.kid(1).kid(0).opCode == Op.REG && logicalShift(((LirFconst) node.kid(1).kid(1)).value) != 0) {
					node.setKid(1, new LirBinOp(node.kid(1).id, Op.LSHS, node.kid(1).type, node.kid(1).kid(0),
							new LirFconst(node.kid(1).kid(1).id, node.kid(1).kid(1).type, logicalShift(((LirFconst) node.kid(1).kid(1)).value), node.kid(1).kid(1).opt), node.kid(1).opt));
				} else if (node.kid(1).kid(1).opCode == Op.REG && logicalShift(((LirIconst) node.kid(1).kid(0)).value) != 0) {
					node.setKid(1, new LirBinOp(node.kid(1).id, Op.LSHS, node.kid(1).type, node.kid(1).kid(1),
							new LirIconst(node.kid(1).kid(0).id, node.kid(1).kid(0).type, logicalShift(((LirIconst) node.kid(1).kid(0)).value), node.kid(1).kid(0).opt), node.kid(1).opt));
				} else if (node.kid(1).kid(1).opCode == Op.REG && logicalShift(((LirFconst) node.kid(1).kid(0)).value) != 0) {
					node.setKid(1, new LirBinOp(node.kid(1).id, Op.LSHS, node.kid(1).type, node.kid(1).kid(1),
							new LirFconst(node.kid(1).kid(0).id, node.kid(1).kid(0).type, logicalShift(((LirFconst) node.kid(1).kid(0)).value), node.kid(1).kid(0).opt), node.kid(1).opt));
				}
				return node;
			case Op.DIVU:
				// Unsigned and signed integers are treated the same here
			case Op.DIVS:
				if (node.kid(1).kid(0).opCode == Op.REG && logicalShift(((LirIconst) node.kid(1).kid(1)).value) != 0) {
					node.setKid(1, new LirBinOp(node.kid(1).id, Op.RSHS, node.kid(1).type, node.kid(1).kid(0),
							new LirIconst(node.kid(1).kid(1).id, node.kid(1).kid(1).type, logicalShift(((LirIconst) node.kid(1).kid(1)).value), node.kid(1).kid(1).opt), node.kid(1).opt));
				} else if (node.kid(1).kid(0).opCode == Op.REG && logicalShift(((LirFconst) node.kid(1).kid(1)).value) != 0) {
					node.setKid(1, new LirBinOp(node.kid(1).id, Op.RSHS, node.kid(1).type, node.kid(1).kid(0),
							new LirFconst(node.kid(1).kid(1).id, node.kid(1).kid(1).type, logicalShift(((LirFconst) node.kid(1).kid(1)).value), node.kid(1).kid(1).opt), node.kid(1).opt));
				}
				return node;
			default:
				throw new Error("Reached unexpected case in evaluating");
		}
	}

	private long logicalShift(long number) {
		if (number == 0) {
			return 0;
		}
		long i = 0;
		// Check whether the number is a power of two.
		while(number != 1) {
			if (number % 2 != 0) {
				// Return 0 in case number is not a power of two.
				return 0;
			}
			number = number / 2;
			i++;
		}
		// If function reaches this point number must be a power of two.
		// -1 because shifting
		return i-1;
	}

	private long logicalShift(double number) {
		if (number == 0) {
			return 0;
		}
		long i = 0;
		// Check whether the number is a power of two.
		while(number != 1) {
			if (number % 2 != 0) {
				// Return 0 in case number is not a power of two.
				return 0;
			}
			number = number / 2;
			i++;
		}
		// If function reaches this point number must be a power of two.
		// -1 because shifting
		return i-1;
	}
}