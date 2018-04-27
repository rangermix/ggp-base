package org.ggp.base.player.gamer.statemachine;

import java.io.Serializable;

import org.apache.lucene.util.OpenBitSet;

public abstract class XNodeAbstract implements Serializable {

	private static final long serialVersionUID = -5238950554773625862L;

	public volatile OpenBitSet state;

}
