package org.ggp.base.player.gamer.statemachine;

import java.io.Serializable;
import java.util.HashMap;
import java.util.List;
import java.util.concurrent.atomic.AtomicBoolean;

import org.apache.lucene.util.OpenBitSet;
import org.ggp.base.util.statemachine.Move;

public class XNodeLight extends XNodeAbstract implements Serializable {


	private static final long serialVersionUID = -8233477291312873815L;
	public XNodeLight(OpenBitSet state, int numRoles) {
		this.state = state;
		this.children = new HashMap<List<Move>, XNodeLight>();
		this.legalJointMoves = new HashMap<Move, List<List<Move>>>();

		this.utility = new double[numRoles];
		this.visits = 0;
		this.updates = 0;
		//this.sum_x = 0;
		//this.sum_x2 = 0;
		//this.n = 0;
		//this.C_CONST = 60;
		this.expanded = false;
	}
	public volatile double[] utility;
	public volatile double visits;
	public volatile double updates;
	public volatile boolean expanded;
	public volatile HashMap<List<Move>, XNodeLight> children;
	//public volatile double sum_x;
	//public volatile double sum_x2;
	//public volatile int n;
	//public volatile double C_CONST;
	//dont serialize these
	public transient volatile AtomicBoolean started = new AtomicBoolean(false);
	public transient volatile HashMap<Move, List<List<Move>>> legalJointMoves;
	public transient volatile Move[] legalMoves;
}