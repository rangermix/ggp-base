package org.ggp.base.player.gamer.statemachine;

import java.io.Serializable;
import java.util.HashMap;
import java.util.List;
import java.util.concurrent.atomic.AtomicBoolean;

import org.apache.lucene.util.OpenBitSet;
import org.ggp.base.util.statemachine.Move;

public class XNode extends XNodeAbstract implements Serializable {

	private static final long serialVersionUID = -9210775452015897511L;

	public XNode(OpenBitSet state) {
		this.started = new AtomicBoolean(false);
		this.state = state;
		this.children = new HashMap<List<Move>, XNode>();
		this.legalJointMoves = new HashMap<Move, List<List<Move>>>();
		this.utility = 0;
		this.visits = 0;
		this.updates = 0;
		this.sum_x = 0;
		this.sum_x2 = 0;
		this.n = 0;
		this.C_CONST = 60;
		this.expanded = false;
		this.solved = false;
		this.solvedValue = 0;
	}
	public volatile double utility;
	public volatile double visits;
	public volatile double updates;
	public volatile Move[] legalMoves;
	public volatile HashMap<List<Move>, XNode> children;
	public volatile HashMap<Move, List<List<Move>>> legalJointMoves;
	public volatile double sum_x;
	public volatile double sum_x2;
	public volatile int n;
	public volatile double C_CONST;
	public volatile boolean expanded;
	public volatile AtomicBoolean started;
	public volatile boolean solved;
	public volatile double solvedValue;
}