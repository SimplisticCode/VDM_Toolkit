package vdm2isa.tr.definitions;

import com.fujitsu.vdmj.tc.annotations.TCAnnotationList;
import com.fujitsu.vdmj.tc.lex.TCNameToken;
import com.fujitsu.vdmj.typechecker.NameScope;

import vdm2isa.tr.definitions.visitors.TRDefinitionVisitor;
import vdm2isa.tr.expressions.TRExpression;
import vdm2isa.tr.patterns.TRPattern;
import vdm2isa.tr.types.TRInvariantType;
import vdm2isa.tr.types.TRRecordType;
import vdm2isa.tr.types.TRType;
import vdm2isa.lex.IsaTemplates;
import vdm2isa.lex.IsaToken;
import vdm2isa.lex.TRIsaVDMCommentList;  

public class TRTypeDefinition extends TRDefinition {
    private static final long serialVersionUID = 1L;

    private final TRInvariantType type;
    private final TRPattern invPattern;
    private final TRExpression invExpression;
    private final TRPattern eqPattern1;
    private final TRPattern eqPattern2;
    private final TRExpression eqExpression;
    private final TRPattern ordPattern1;
    private final TRPattern ordPattern2;
    private final TRExpression ordExpression;
	
    private final TRExplicitFunctionDefinition invdef;
    private final TRExplicitFunctionDefinition eqdef;
    private final TRExplicitFunctionDefinition orddef;
    private final TRExplicitFunctionDefinition mindef;
    private final TRExplicitFunctionDefinition maxdef;
    
    private boolean infinite; 
	private TRDefinitionList composeDefinitions;

    public TRTypeDefinition(TRIsaVDMCommentList comments, 
        TCAnnotationList annotations, 
        TCNameToken name, 
        NameScope nameScope,
        boolean used,
        boolean excluded,
        TRInvariantType type,
        TRPattern invPattern,  
        TRExpression invExpression,
        TRPattern eqPattern1,
        TRPattern eqPattern2,
        TRExpression eqExpression,
        TRPattern ordPattern1,
        TRPattern ordPattern2,
        TRExpression ordExpression,
        TRExplicitFunctionDefinition invdef,
        TRExplicitFunctionDefinition eqdef,
        TRExplicitFunctionDefinition orddef,
        TRExplicitFunctionDefinition mindef,
        TRExplicitFunctionDefinition maxdef,
        boolean infinite,
        TRDefinitionList composeDefinitions
        )
    {
        super(name.getLocation(), comments, annotations, name, nameScope, used, excluded);
        this.type = type;
        this.invPattern = invPattern;
        this.invExpression = invExpression;
        this.eqPattern1 = eqPattern1;
        this.eqPattern2 = eqPattern2;
        this.eqExpression = eqExpression;
        this.ordPattern1 = ordPattern1;
        this.ordPattern2 = ordPattern2;
        this.ordExpression = ordExpression;
        this.invdef = invdef;
        this.eqdef = eqdef;
        this.orddef = orddef;
        this.mindef = mindef;
        this.maxdef = maxdef;
        this.infinite = infinite;
        this.composeDefinitions = composeDefinitions;
        //System.out.println(toString());
    }

    @Override
	public String toString()
	{
		return "TRTypeDef for \"" + name.toString() + 
			"\" type " + type.toString() + 
            " inv " + String.valueOf(invExpression);
	}

    @Override
    public IsaToken isaToken()
    {
        return IsaToken.TYPEOF;
    }

    @Override 
    public String translate()
    {
        StringBuilder sb = new StringBuilder();
        sb.append(super.translate());
        // TLD for records
        if (type instanceof TRRecordType)
        {
            TRRecordType trtype = (TRRecordType)type;
            
            // translate record definition 
            sb.append(trtype.isaToken().toString() + " "); 
            sb.append(trtype.translate());
            sb.append(" ");
            sb.append(IsaToken.EQUALS.toString());
            sb.append(" ");
            sb.append(getFormattingSeparator());
            sb.append(trtype.getFields().translate());
            sb.append(getFormattingSeparator() + getFormattingSeparator());

            // translate implicit record type invariant
            String varName = IsaToken.dummyVarNames(1, name.getLocation());
            sb.append(IsaTemplates.translateInvariantDefinition(getLocation(),
                    name.toString(), name.toString(), varName, 
                    trtype.invTranslate(varName), false));            
        }
        //TODO user defined invariant on TLD 
        return sb.toString();
    }

    @Override
    public String invTranslate() {
        // TODO Auto-generated method stub
        return null;
    }

	@Override
	public <R, S> R apply(TRDefinitionVisitor<R, S> visitor, S arg)
	{
		return visitor.caseTypeDefinition(this, arg);
	}

	public TRExpression getInvExpression()
	{
		return null;	// TODO!
	}

	public TRExpression getEqExpression()
	{
		return null;	// TODO!
	}

	public TRExpression getOrdExpression()
	{
		return null;	// TODO!
	}

	public TRType getType()
	{
		return type;
	}
}
