package vdm2isa.tr.types;

import com.fujitsu.vdmj.tc.types.TCFieldList;
import com.fujitsu.vdmj.tc.types.TCField;

import vdm2isa.lex.IsaTemplates;
import vdm2isa.lex.IsaToken;
import vdm2isa.tr.TRMappedList;

public class TRFieldList extends TRMappedList<TCField, TRField>
{
	private static final long serialVersionUID = 1L;
	
	public TRFieldList()
	{
		super();
	}

	public TRFieldList(TCFieldList list) throws Exception
	{
		super(list);
	}

    public String invTranslate(String varName)
    {
        StringBuilder sb = new StringBuilder();

		if (!this.isEmpty())
		{
			sb.append(this.get(0).invTranslate(varName));

			for (int i = 1; i < this.size(); i++)
			{
				sb.append(" ");
                sb.append(IsaToken.AND.toString());
                sb.append("\n\t\t ");
				sb.append(this.get(i).invTranslate(varName));
			}
		}

		return sb.toString();  
    }

	public String translate()
	{
		return IsaTemplates.listToString(this, "\n\t");
	}
}