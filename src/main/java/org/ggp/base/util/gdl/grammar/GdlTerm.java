package org.ggp.base.util.gdl.grammar;

public abstract class GdlTerm extends Gdl
{
	private static final long serialVersionUID = -2332225469048642997L;

	@Override
	public abstract boolean isGround();

	public abstract GdlSentence toSentence();

	@Override
	public abstract String toString();

}
