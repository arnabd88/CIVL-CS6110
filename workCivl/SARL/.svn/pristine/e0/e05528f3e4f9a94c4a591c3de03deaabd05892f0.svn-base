package edu.udel.cis.vsl.sarl.prove.cvc;

import java.util.List;

import edu.udel.cis.vsl.sarl.util.FastList;

/**
 * 
 * This class is used to deal with div or modulo during the cvc translation
 * Since cvc4 currently can not deal with div or modulo, div or modulo is 
 * translated into the form : value && constraints. value is the actual value of
 * the division or modulo operation (e.g., the value of the division is the quotient).
 * The format of the constraints can be read below.
 * 
 * 
 * @author yanyihao
 * 
 */
public class Translation {
	/**
	 * store the translation result
	 */
	private FastList<String> result;
	
	/**
	 * is the translation coming from division or module?
	 */
	private Boolean isDivOrModulo;
	
	/**
	 * if the translation comes from division or module,
	 * side-effects will be generated, then the side effects
	 * will be conjunct as a single fast list:
	 * e.g.
	 * the side effects of x%y will be:
	 * (y*t__0 + t__1 = x) && (sign(x) = sign(t__1) || t__1=0) && (|t__1| < |y|)
	 * 
	 * sign(t__1) = sign(x) ==>
	 * (t__1>0 && x>0) || (t__1<0 && x<0)
	 * 
	 *|t__1| < |y| ==>
	 *(
	 *(t__1 >0 && y>0 && y>t__1) ||
	 *(t__1 >0 && y<0 && 0 - y > t__1) ||
	 *(t__1 <0 && y<0 && t__1 > y) ||
	 *(t__1<0 && y>0 && 0 - y < t__1)
	 *)
	 * 
	 */
	private FastList<String> auxConstraints;
	/**
	 * store all the aux vars generated and used in the result and
	 * side effects.
	 */
	private List<FastList<String>> auxVars;
	
	public Translation(){
		result = new FastList<String>();
		isDivOrModulo = false;
		auxConstraints = null;
		auxVars = null;
	}
	
	public Translation(FastList<String> res){
		result = res;
		isDivOrModulo = false;
		auxConstraints = null;
		auxVars = null;
	}
	
	public Translation(FastList<String> res, Boolean isDvOrMo, 
			FastList<String> auxConstraints, List<FastList<String>> auxVars){
		result = res;
		isDivOrModulo = isDvOrMo;
		this.auxConstraints = auxConstraints;
		this.auxVars = auxVars;
	}
	
	public FastList<String> getResult() {
		return result;
	}



	public Boolean getIsDivOrModulo() {
		return isDivOrModulo;
	}



	public void setIsDivOrModulo(Boolean isDivOrModule) {
		this.isDivOrModulo = isDivOrModule;
	}



	public FastList<String> getAuxConstraints() {
		return auxConstraints;
	}



	public void setAuxConstraints(FastList<String> auxConstraints) {
		this.auxConstraints = auxConstraints;
	}



	public List<FastList<String>> getAuxVars() {
		return auxVars;
	}



	public void setAuxVars(List<FastList<String>> auxVars) {
		this.auxVars = auxVars;
	}

	public Translation clone(){
		FastList<String> constraints = this.auxConstraints == null ? null :
				this.auxConstraints.clone();
		Translation translation = new Translation(this.result.clone(),
				this.isDivOrModulo, 
				constraints, 
				this.auxVars);
		return translation;
	}

	@Override
	public String toString() {
		return result.toString();
	}
}
