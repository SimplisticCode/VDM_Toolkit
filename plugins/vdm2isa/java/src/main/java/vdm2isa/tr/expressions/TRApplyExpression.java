/*******************************************************************************
 *	Copyright (c) 2020 Leo Freitas.
 ******************************************************************************/

package vdm2isa.tr.expressions;

import vdm2isa.lex.IsaTemplates;
import vdm2isa.lex.IsaToken;

public class TRApplyExpression extends TRExpression
{
	private static final long serialVersionUID = 1L;
	private final TRExpression root;
	private final TRExpressionList args;
	
	public TRApplyExpression(TRExpression root, TRExpressionList args)
	{
		super(root);
		this.root = root;
		this.args = args;
		this.args.separator = " ";
	}

	@Override
	public String translate()
	{
		assert this.args.separator != null;
		return "(" + root.translate() + this.args.separator + args.translate() + ")";
	}

	@Override
	public IsaToken isaToken() {
		return IsaToken.APPLY;
	}
}
