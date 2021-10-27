package vdm2isa.tr.expressions;

import com.fujitsu.vdmj.tc.lex.TCIdentifierToken;

import vdm2isa.lex.IsaToken;

public class TRRecordModifier extends TRExpression 
{
    private static final long serialVersionUID = 1L;
    private final TCIdentifierToken tag;
    private final TRExpression value; 

    public TRRecordModifier(TCIdentifierToken tag, TRExpression value)
    {
        super(tag.getLocation());
        this.tag = tag;
        this.value = value;
    }

    @Override
    public IsaToken isaToken() {
        return IsaToken.RECORD_MODIFIER;
    }

    @Override
    public String translate() {
        return tag.toString() + isaToken().toString() + value.translate();
    }
            
}