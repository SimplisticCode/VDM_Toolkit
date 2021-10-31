package vdm2isa.tr.expressions;

import com.fujitsu.vdmj.tc.lex.TCIdentifierToken;

import vdm2isa.lex.IsaTemplates;
import vdm2isa.lex.IsaToken;
import vdm2isa.tr.expressions.visitors.TRExpressionVisitor;

public class TRFieldExpression extends TRExpression {
    
	private static final long serialVersionUID = 1L;
    private final TRExpression object;
    private final TCIdentifierToken field; 

    public TRFieldExpression(TRExpression object, TCIdentifierToken field)
    {
        super(object);
        this.object = object;
        this.field = field;
        //System.out.println(toString());
    }

    @Override
    public IsaToken isaToken() {
        return IsaToken.POINT; 
    }

    @Override
    public String translate() {
        // attempt to get underlying object record type name to change record field name according to TRRecordType TLD considerations 
        return IsaToken.parenthesise(
                    IsaTemplates.isabelleRecordFieldName(object.getRecordTypeName(), field.getName()) + " " +
                    IsaToken.parenthesise(object.translate())
                );
    }

	@Override
	public <R, S> R apply(TRExpressionVisitor<R, S> visitor, S arg)
	{
		return visitor.caseFieldExpression(this, arg);
	}
}
