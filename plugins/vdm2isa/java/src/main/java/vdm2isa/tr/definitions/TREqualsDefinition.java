package vdm2isa.tr.definitions;

import com.fujitsu.vdmj.lex.LexLocation;
import com.fujitsu.vdmj.tc.annotations.TCAnnotationList;
import com.fujitsu.vdmj.tc.definitions.TCDefinition;
import com.fujitsu.vdmj.tc.definitions.TCEqualsDefinition;
import com.fujitsu.vdmj.typechecker.NameScope;

import vdm2isa.lex.IsaToken;
import vdm2isa.lex.TRIsaVDMCommentList;
import vdm2isa.messages.IsaErrorMessage;
import vdm2isa.tr.definitions.visitors.TRDefinitionVisitor;
import vdm2isa.tr.expressions.TRExpression;
import vdm2isa.tr.patterns.TRMultipleBind;
import vdm2isa.tr.patterns.TRMultipleTypeBind;
import vdm2isa.tr.patterns.TRPattern;
import vdm2isa.tr.types.TRType;

public class TREqualsDefinition extends TRValueDefinition {

    private final TRMultipleTypeBind typebind;
    private final TRMultipleBind bind;

    public TREqualsDefinition(TCEqualsDefinition definition, LexLocation location, TRIsaVDMCommentList comments, 
            TCAnnotationList annotations, NameScope nameScope, boolean used, boolean excluded,
            TRPattern pattern, TRMultipleTypeBind typebind, TRMultipleBind bind, TRExpression test,
            TRType expType, TRType defType, TRDefinitionList defs) {
        super(definition, location, comments, annotations, nameScope, used, excluded, pattern, defType, test, expType, defs);
        this.typebind = typebind;
        this.bind = bind;
        //setLocal(true); //leave to NameScope?
        if (pattern == null && typebind == null)
            report(IsaErrorMessage.VDMSL_INVALID_VALUEDEF_3P, "equals", "structure", "cannot have null pattern and type bind");
        //System.out.println(toString());
    }

    @Override
    public String toString()
    {
        return "EqDef " + 
            "\n\t patt = " + String.valueOf(getPattern()) + 
            "\n\t typb = " + String.valueOf(typebind) + 
            "\n\t bind = " + String.valueOf(bind) +
            "\n\t test = " + String.valueOf(getExp()) +
            "\n\t expT = " + String.valueOf(getExpType()) + 
            "\n\t defT = " + String.valueOf(getType()) + 
            "\n\t defs = " + String.valueOf(getDefs()) +
            "\n\t loc  = " + String.valueOf(getLocation()); 
    }

    @Override
    public <R, S> R apply(TRDefinitionVisitor<R, S> visitor, S arg) {
        return visitor.caseEqualsDefinition(this, arg);
    }

    @Override
    public IsaToken isaToken() {
        return IsaToken.EQUALS;
    }

    /**
     * Either it's pattern equality (e.g., mk_R(x,y) = r) or a typed equality (e.g. x: nat = 10); 
     * former, take pattern's view; latter, take the type bind pattern view, which *must* be singleton
     */
    @Override
    public String getDeclaredName()
    {
        assert typebind.plist.size() == 1;
        return getPattern() != null ? getPattern().translate() : typebind.plist.translate();    
    }
}