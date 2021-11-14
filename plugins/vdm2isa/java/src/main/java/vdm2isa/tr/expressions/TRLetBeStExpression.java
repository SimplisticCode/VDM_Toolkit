package vdm2isa.tr.expressions;

import com.fujitsu.vdmj.ast.lex.LexKeywordToken;
import com.fujitsu.vdmj.ast.lex.LexToken;
import com.fujitsu.vdmj.lex.LexLocation;
import com.fujitsu.vdmj.lex.Token;
import com.fujitsu.vdmj.tc.lex.TCNameToken;
import com.fujitsu.vdmj.typechecker.NameScope;

import vdm2isa.lex.IsaToken;
import vdm2isa.tr.definitions.TRLocalDefinition;
import vdm2isa.tr.definitions.TRMultiBindListDefinition;
import vdm2isa.tr.expressions.visitors.TRExpressionVisitor;
import vdm2isa.tr.patterns.TRMultipleBind;
import vdm2isa.tr.types.TRSetType;
import vdm2isa.tr.types.TRType;

/**
 * LetBeStExpressions are complicated. Their target mapping in Isabelle is the Epsilon/SOME operator via axiom of choice. 
 * Nevertheless, that operator does not allow multiple binds neither a result relative to a value expression. So for example
 * 
 * let x in S be st P(x) in x = (SOME x . x : S /\ P(x))
 * 
 * But then 
 * 
 * let x, y in S be st P(x,y) in exp(x,y) = ?
 * 
 * Therefore, we decided to use set comprehension to represent the let, and choose from the resulting set the value choice as
 * 
 * let x, y in S be st P(x,y) in exp(x,y) = (SOME v . v : { exp(x,y) | x y . x : S /\ y : S /\ P(x,y) })
 */
public class TRLetBeStExpression extends TRVDMLocalDefinitionListExpression {
    
    private static final long serialVersionUID = 1L;
    private final TRMultipleBind bind;
    private final TRExpression suchThat;
    private final TRMultiBindListDefinition def;
    private final TRBinaryExpression vInSetS;

	public TRLetBeStExpression(LexLocation location, TRMultipleBind bind, TRExpression suchThat, TRExpression value, TRMultiBindListDefinition def, TRType exptype) {
        super(location, value, exptype);
        this.bind = bind;
        this.suchThat = suchThat;
        this.def = def; 
        // LetBeSt is represented through in set of a set comprehension constructed on the fly, with necessary adjustments to exptype for the set comp.
        String original = IsaToken.dummyVarNames(1, location);
        TCNameToken name = new TCNameToken(location, location.module, original);
        this.vInSetS = new TRBinaryExpression(
            new TRVariableExpression(location, name, original, new TRLocalDefinition(location, null, null, name, NameScope.LOCAL, true, false, exptype), exptype), 
            new LexKeywordToken(Token.INSET, location), 
            new TRSetCompExpression(location, value, bind.getMultipleBindList(), suchThat, new TRSetType(location, exptype.definitions, exptype, false)), exptype);
    }

    @Override
    protected void setup()
	{
        super.setup();
        setFormattingSeparator("\n\t\t");
	 	setInvTranslateSeparator(" " + IsaToken.AND.toString() + " ");
	}

    @Override
    public String toString()
    {
        return "LetBeStDef " + String.valueOf(bind) + " be st " + 
            String.valueOf(suchThat) + " in \n\t" + String.valueOf(expression);
    }

    @Override
    public IsaToken isaToken() {
       return IsaToken.SOME;
    }

    public String translate() {
        StringBuilder sb = new StringBuilder();
        sb.append(getFormattingSeparator());
        sb.append(isaToken().toString());
        sb.append(IsaToken.SPACE);
        sb.append(IsaToken.dummyVarNames(1, location));
        sb.append(IsaToken.SPACE);
        sb.append(IsaToken.POINT);
        //TODO someone has to call the inner binds record translate? 
        sb.append(this.vInSetS.translate());
        return IsaToken.parenthesise(sb.toString());
    }

    /**
     * invariant translation is based on the binds' type(s).
     */
    @Override
    public String localInvTranslate()
    {
        return bind.invTranslate();
    }

	@Override
	public <R, S> R apply(TRExpressionVisitor<R, S> visitor, S arg)
	{
		return visitor.caseLetBeStExpression(this, arg);
	}
}
