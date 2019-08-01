package core;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;
import java.util.HashSet;

import soot.Local;
import soot.SootField;
import soot.Unit;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;

class AssignConstraint {
	Local from, to;
	AssignConstraint(Local from, Local to) {
		this.from = from;
		this.to = to;
	}
}

class NewConstraint {
	Local to;
	int allocId;
	NewConstraint(int allocId, Local to) {
		this.allocId = allocId;
		this.to = to;
	}
}

// class' Fields and its point set
class ClassFieldsPointSet {
	Local base;
	Map<SootField, HashSet<Local> > fieldsPointSet;

	public ClassFieldsPointSet() {
		this.fieldsPointSet = new HashMap<>();
	}

	public ClassFieldsPointSet(Local base) {
		this.base = base;
		this.fieldsPointSet = new HashMap<>();
	}

	public boolean containsKey(SootField field) {
		return fieldsPointSet.containsKey(field);
	}

	public void addFieldPointTo(SootField field, Local pointTo) {
		if (!fieldsPointSet.containsKey(field)) {
			HashSet<Local> pointSet = new HashSet<>();
			pointSet.add(pointTo);
			fieldsPointSet.put(field, pointSet);
		} else {
			fieldsPointSet.get(field).add(pointTo);
		}
	}

	public HashSet<Local> getPointSet(SootField field) {
		return fieldsPointSet.get(field);
	}
}

// all classes
class AllClassesWithFields {
	Map<Local, ClassFieldsPointSet> allClasses;

	AllClassesWithFields() {
		this.allClasses = new HashMap<>();
	}

	public void setClassAndFields(Local base, SootField field, Local pointTo) {
		if (!allClasses.containsKey(base)) {
			ClassFieldsPointSet temp = new ClassFieldsPointSet(base);
			temp.addFieldPointTo(field, pointTo);
			allClasses.put(base, temp);
		} else {
			allClasses.get(base).addFieldPointTo(field, pointTo);
		}
	}

	public HashSet<Local> getFieldPointSet(Local base, SootField field) {
		if (!allClasses.containsKey(base)) {
			throw new NullPointerException();
		} else {
			return allClasses.get(base).getPointSet(field);
		}
	}

	public void assign(Local from, Local to) {
		ClassFieldsPointSet temp = allClasses.get(from);
		allClasses.put(to, temp);
	}

	public boolean isConstainsBase(Local base) {
		if (allClasses.containsKey(base)) {
			return true;
		} else {
			return false;
		}
	}

	public boolean isConstainsField(Local base, SootField field) {
		if (allClasses.containsKey(base)) {
			return allClasses.get(base).containsKey(field);
		} else {
			return false;
		}
	}

}

public class Anderson {
	private List<AssignConstraint> assignConstraintList = new ArrayList<AssignConstraint>();

	private List<NewConstraint> newConstraintList = new ArrayList<NewConstraint>();

	Map<Local, TreeSet<Integer>> pts = new HashMap<Local, TreeSet<Integer>>();

	AllClassesWithFields allClassesWithFields = new AllClassesWithFields();
	// 存assign方法的实参
	public List<Local> assignRealParametersList = new ArrayList<>();
	// Local 到 Real 的映射
	Map<Local, Local> assignLocalToRealMap = new HashMap<>();
	// temp 指向集
	Map<Local, HashSet<Local> > tempPointSet = new HashMap<>();


	void clearAssignParametersList() {
		this.assignRealParametersList.clear();
	}
	void storeAssignParameters(Local parameter) {
		this.assignRealParametersList.add(parameter);
	}

	void mapLocalToReal(Local local, int parameter_idx) {
		assignLocalToRealMap.put(local, assignRealParametersList.get(parameter_idx));
	}

	// assign $r3
	void getTempPointSet(Unit u) {
		DefinitionStmt defU = (DefinitionStmt) u;
		HashSet<Local> temp = new HashSet<>();
		Local rightBase = (Local) ((InstanceFieldRef) defU.getRightOp()).getBase();
		SootField rightField = ((InstanceFieldRef) defU.getRightOp()).getField();
		Local rightReal = this.assignLocalToRealMap.get(rightBase);

		//System.out.println("getTempPointSet: ");
		//System.out.println("rightBase: " + rightBase.toString());
		//System.out.println("rightReal: " + rightReal.toString());
		//System.out.println("rightField: " + rightField.toString());
		//System.out.println("leftLocal: " + defU.getLeftOp().toString());

		if (!this.allClassesWithFields.isConstainsField(rightReal, rightField)) {
			throw new NullPointerException();
		} else {
			for (Local pointed : this.allClassesWithFields.getFieldPointSet(rightReal, rightField) ) {
				temp.add(pointed);
			}
			this.tempPointSet.put((Local) defU.getLeftOp(), temp);
		}
	}

	// get $r3
	void assignTempPointSetToReal(Unit u) {
		DefinitionStmt defU = (DefinitionStmt) u;
		HashSet<Local> tempPointSet;
		Local temp = (Local) defU.getRightOp();
		Local leftBase = (Local) ((InstanceFieldRef) defU.getLeftOp()).getBase();	
		SootField leftField = ((InstanceFieldRef) defU.getLeftOp()).getField();
		Local leftReal = this.assignLocalToRealMap.get(leftBase);

		//System.out.println("assignTempPointSetReal: ");
		//System.out.println("leftReal: " + leftReal.toString());

		if (!this.tempPointSet.containsKey(temp)) {
			throw new NullPointerException();
		} else {
			tempPointSet = this.tempPointSet.get(temp);
			for (Local pointed : tempPointSet) {
				this.allClassesWithFields.setClassAndFields(leftReal, leftField, pointed);
			}
		}
	} 

	void addAssignConstraint(Local from, Local to) {
		assignConstraintList.add(new AssignConstraint(from, to));
	}

	void addNewConstraint(int alloc, Local to) {
		newConstraintList.add(new NewConstraint(alloc, to));		
	}

	void run() {
		for (NewConstraint nc : newConstraintList) {
			if (!pts.containsKey(nc.to)) {
				pts.put(nc.to, new TreeSet<Integer>());
			}
			pts.get(nc.to).add(nc.allocId);
		}
		for (boolean flag = true; flag; ) {
			flag = false;
			for (AssignConstraint ac : assignConstraintList) {
				if (!pts.containsKey(ac.from)) {
					continue;
				}	
				if (!pts.containsKey(ac.to)) {
					pts.put(ac.to, new TreeSet<Integer>());
				}
				if (pts.get(ac.to).addAll(pts.get(ac.from))) {
					flag = true;
				}
			}
		}
	}

	TreeSet<Integer> getPointsToSet(Local local) {
		return pts.get(local);
	}
	
}
