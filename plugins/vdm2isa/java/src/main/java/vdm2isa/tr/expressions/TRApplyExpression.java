/*******************************************************************************
 *	Copyright (c) 2020 Leo Freitas.
 ******************************************************************************/

package vdm2isa.tr.expressions;

import vdm2isa.lex.IsaToken;
import vdm2isa.tr.types.TRSeqType;
import vdm2isa.tr.types.TRType;

public class TRApplyExpression extends TRExpression
{
	private static final long serialVersionUID = 1L;
	private final TRType type;
	private final TRExpression root;
	private final TRExpressionList args;
	
	public TRApplyExpression(TRType type, TRExpression root, TRExpressionList args)
	{
		super(root);
		this.type = type;
		this.root = root;
		this.args = args;
		//@todo depending on the root:  map(x) is different from list(x) etc.? 
		this.args.separator = type instanceof TRSeqType ? 
			IsaToken.SEQAPPLY.toString() : IsaToken.APPLY.toString();
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
