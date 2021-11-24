package vdm2isa.tr.expressions;

import java.util.Arrays;

import com.fujitsu.vdmj.tc.expressions.TCCaseAlternative;
import com.fujitsu.vdmj.tc.expressions.TCCaseAlternativeList;

import vdm2isa.lex.IsaToken;
import vdm2isa.tr.TRMappedList;
import vdm2isa.tr.types.TRTypeSet;

public class TRCaseAlternativeList extends TRMappedList<TCCaseAlternative, TRCaseAlternative> {
	private static final long serialVersionUID = 1L;
    
    protected TRCaseAlternativeList()
    {
        super();
    }

    public TRCaseAlternativeList(TRCaseAlternativeList from)
	{
		this();
		addAll(from);
	}

    public TRCaseAlternativeList(TCCaseAlternativeList from) throws Exception
    {
        super(from);
    }

    /**
	 * Choose the first element type (could have been any); this is to attempt to solve the "(the (pattern))" problem
	 */
	public TRTypeSet getTypes()
	{
        TRTypeSet result = new TRTypeSet();
        for (TRCaseAlternative c : this)
        {
            result.add(c.getType());
        }
		return result;
	}

    @Override
    protected void setup()
    {
        super.setup();
        setFormattingSeparator("\n\t\t\t ");
        setSemanticSeparator(IsaToken.BAR.toString() + " ");
    }

	public static String translate(TRCaseAlternative... args)
	{
		TRCaseAlternativeList list = new TRCaseAlternativeList();
        list.addAll(Arrays.asList(args));
		return list.translate();	
	}
}
