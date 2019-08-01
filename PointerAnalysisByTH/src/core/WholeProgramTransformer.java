package core;

import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;

import java.util.TreeMap;
import java.util.TreeSet;

import soot.Local;
import soot.MethodOrMethodContext;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.util.queue.QueueReader;

import soot.jimple.*;

public class WholeProgramTransformer extends SceneTransformer {
	
	@Override
	protected void internalTransform(String arg0, Map<String, String> arg1) {
		
		TreeMap<Integer, Local> queries = new TreeMap<Integer, Local>();
		Anderson anderson = new Anderson(); 
		
		ReachableMethods reachableMethods = Scene.v().getReachableMethods();
		QueueReader<MethodOrMethodContext> qr = reachableMethods.listener();		
		while (qr.hasNext()) {
			SootMethod sm = qr.next().method();

			if (sm.toString().contains("test.")) {
				//System.out.println(sm);
				int allocId = 0;
				if (sm.hasActiveBody()) {

					for (Unit u : sm.getActiveBody().getUnits()) {
						//System.out.println("S: " + u);
						//System.out.println(u.getClass());

						if (u instanceof InvokeStmt) {
							InvokeExpr ie = ((InvokeStmt) u).getInvokeExpr();

							if ((ie instanceof SpecialInvokeExpr) && ie.getArgCount() > 0) {
								// A a = new A(b)
								if (ie.getMethod().toString().contains("init")) {
									if (ie.getMethod().hasActiveBody()) {

										//System.out.print("init sm: " + sm.toString());
										//System.out.print("init ie: " + ie.toString());

										SpecialInvokeExpr sie = (SpecialInvokeExpr) ie;
										Local base = (Local) sie.getBase();
									
										for (Unit subUnit : ie.getMethod().getActiveBody().getUnits()) {
											//这里参数可以设为多个
											if (subUnit instanceof DefinitionStmt) {
												DefinitionStmt defSubUnit = (DefinitionStmt) subUnit;

												if(defSubUnit.getLeftOp() instanceof InstanceFieldRef && defSubUnit.getRightOp() instanceof Local){
													
													// r0.<benchmark.objects.A: benchmark.objects.B f> = r1;
													if(!defSubUnit.getRightOp().toString().contains("$")){

														//System.out.println("sie base: " + base.toString() );
														// this.f
														anderson.allClassesWithFields.setClassAndFields(base, ((InstanceFieldRef)(defSubUnit.getLeftOp())).getField(), (Local) sie.getArg(0) );
													}
												}
											}
										}
									}
									
								} else if (ie.getMethod().toString().contains("assign")) {
									// 清空缓存参数
									anderson.clearAssignParametersList();

									//System.out.print("init sm: " + sm.toString());
									//System.out.println("assign ie: " + ie.toString());

									// store assign real parameters a c
									for (int i = 0; i < ie.getArgCount(); i++) {
										anderson.storeAssignParameters((Local) ie.getArg(i));
									}
									if (ie.getMethod().hasActiveBody()) {
										for (Unit subUnit : ie.getMethod().getActiveBody().getUnits()) {
											if (subUnit instanceof DefinitionStmt) {
												DefinitionStmt defSubUnit = (DefinitionStmt) subUnit;
												// map local to real
												// r1 -> a ; r2 -> c
												for (int i = 0; i < anderson.assignRealParametersList.size(); i++) {
													if (defSubUnit.getRightOp().toString().contains("@parameter" + i) ) {
														//System.out.println("defSubUnit: " + defSubUnit.getLeftOp().toString() + " i: " + i);

														anderson.mapLocalToReal((Local) defSubUnit.getLeftOp(), i);
													}
												}
												// get temp point set 
												if (defSubUnit.getLeftOp().toString().contains("$") && defSubUnit.getRightOp() instanceof InstanceFieldRef) {
													anderson.getTempPointSet(subUnit);
												}
												// assign temp to real
												if (defSubUnit.getRightOp().toString().contains("$") && defSubUnit.getLeftOp() instanceof InstanceFieldRef) {
													anderson.assignTempPointSetToReal(subUnit);
												}

											}
										}
									}
								}
							}

							if (ie.getMethod().toString().equals("<benchmark.internal.Benchmark: void alloc(int)>")) {
								if(ie.getArgs().size() > 0)
                                	allocId = ((IntConstant) ie.getArgs().get(0)).value;
                            	else
                            	    allocId = 0;
							}
							if (ie.getMethod().toString().equals("<benchmark.internal.Benchmark: void test(int,java.lang.Object)>")) {
								Value v = ie.getArgs().get(1);
								int id = ((IntConstant)ie.getArgs().get(0)).value;
								queries.put(id, (Local)v);
							}
						}

						/* */
						if (u instanceof DefinitionStmt) {
							DefinitionStmt defU = (DefinitionStmt) u;

							// new
							if (defU.getRightOp() instanceof NewExpr) {
								//System.out.println("allocId: " + allocId + " " + defU.getLeftOp().toString()+ defU.getRightOp().toString());
								anderson.addNewConstraint(allocId, (Local) defU.getLeftOp());
							}

							// a = b
							if (defU.getLeftOp() instanceof Local && defU.getRightOp() instanceof Local) {
								if (anderson.allClassesWithFields.isConstainsBase((Local) defU.getRightOp())) {
									//System.out.print("local assign: " + defU.toString());

									anderson.allClassesWithFields.assign((Local) defU.getRightOp(), (Local) defU.getLeftOp());
								}
								anderson.addAssignConstraint((Local)defU.getRightOp(), (Local) defU.getLeftOp());
							}

							// a = b.f
							if (defU.getLeftOp() instanceof Local && defU.getRightOp() instanceof InstanceFieldRef && !defU.getLeftOp().toString().contains("$")) {
								if (sm.toString().contains("test.")) {
									Local rightBase = (Local) ((InstanceFieldRef) defU.getRightOp()).getBase();

									SootField rightField = ((InstanceFieldRef) defU.getRightOp()).getField();

									//System.out.println("left Local right InstanceFieldRef : ");
									//System.out.println(defU.toString());

									if (!anderson.allClassesWithFields.isConstainsField(rightBase, rightField)) {
										throw new NullPointerException();
									} else {
										HashSet<Local> temp = anderson.allClassesWithFields.getFieldPointSet(rightBase, rightField);
										for (Local e : temp) {
											anderson.addAssignConstraint(e, (Local) defU.getLeftOp());
										}
									}
								}
							}

							// a.f = b
							if (defU.getLeftOp() instanceof InstanceFieldRef && defU.getRightOp() instanceof Local) {
								Local Base = (Local) ((InstanceFieldRef) defU.getLeftOp()).getBase();
								SootField field = ((InstanceFieldRef) defU.getLeftOp()).getField();
								// 这里改为 defU.getRightOp的指向集 看精确度
								anderson.allClassesWithFields.setClassAndFields(Base, field, (Local) defU.getRightOp());
							}

							// a.f = b.f
							if (defU.getLeftOp() instanceof InstanceFieldRef && defU.getRightOp() instanceof InstanceFieldRef) {
								Local leftBase = (Local) ((InstanceFieldRef) defU.getLeftOp()).getBase();
								SootField leftField =  ((InstanceFieldRef) defU.getLeftOp()).getField();
								Local rightBase = (Local) ((InstanceFieldRef) defU.getRightOp()).getBase();
								SootField rightField = ((InstanceFieldRef) defU.getRightOp()).getField();
								HashSet<Local> temp;
								if(anderson.allClassesWithFields.isConstainsField(rightBase, rightField)){
									temp = anderson.allClassesWithFields.getFieldPointSet(rightBase, rightField);
									for(Local e: temp){
										anderson.allClassesWithFields.setClassAndFields(leftBase, leftField, e);
									}
								}
								else{
									throw new NullPointerException();
								}
							}
						}
					}
				}
			}
		}
		
		anderson.run();
		String answer = "";
		for (Entry<Integer, Local> q : queries.entrySet()) {
			TreeSet<Integer> result = anderson.getPointsToSet(q.getValue());
			answer += q.getKey().toString() + ":";
			for (Integer i : result) {
				answer += " " + i;
			}
			answer += "\n";
		}
		AnswerPrinter.printAnswer(answer);
		
	}

}
