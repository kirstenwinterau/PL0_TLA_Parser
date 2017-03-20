package tla;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashSet;
import java.util.Set;

import syms.Constants;
import syms.Type;

/**
 * Represents a TLA+ module for an operation/line of code
 */
public class Module {
    /** Variable and constant info */
    public VariableList constants;
    public VariableList variables;
    /** List of formulas generated (for each line of code) */
    private List<Formula> logic;
    /** Init formula corresponding to each formula in 'logic' */
    private List<Formula> init;
    /** Init formula for the other thread corresponding to each formula in 'logic'*/
    private List<Formula> initD;
    /** True and false conditions - used for loop conditions etc */
    private Formula trueCondition;
    private Formula falseCondition;
    /** List of modules that this module extends (e.g. Naturals, FiniteSequences) */
    private HashSet<String> extendsModules;

    /** Module is initially empty */
    public Module() {
        logic = new ArrayList<Formula>();
        init = new ArrayList<Formula>();
        constants = new VariableList("CONSTANT");
        variables = new VariableList("VARIABLE");
        extendsModules = new HashSet<String>();
        extendsModules.add("Naturals");
        initD = new ArrayList<Formula>();
    }
    public List<Formula> getPredicateList() {
        return logic;
    }
    public void addInit(Formula p) {
        init.add(p);
    }
    public List<Formula> getInit() {
        return init;
    }
    public void extendsModule(String module) {
        if(!extendsModules.contains(module)) {
            extendsModules.add(module);
        }
    }
    public Set<String> getExtendsModules() {
        return extendsModules;
    }
    public void setConstantList(VariableList list) {
        constants = list;
    }
    
    public void setInitD(List<Formula> initD) {
        this.initD = initD;
    }
    public void setVariableList(VariableList list) {
        variables = list;
    }
    /*
     * Encapsulate the given logic in a program counter requirement, resulting in
     * the same form we expect from the user input invariants e.g. (pc=1 => logic)
     */
    private String addPcConstraint(int pc, String logic) {
        String result = "";
        result += "(";
        result += "pc = " + pc;
        result += " => (" + logic + ")";
        result += ")";
        return result;
    }
    /*
     * Print the 'EXTENDS' line of the module (e.g. EXTENDS Naturals)
     */
    private static String printExtends(Set<String> extendsModules) {
        // Assumes there is at least one module we will extend (naturals)
        String result = "EXTENDS ";
        for(String module: extendsModules) {
            result += module;
            result += ", ";
        }
        result = result.substring(0, result.length() - 2);
        result += System.lineSeparator();
        return result;
    }
    
    // For each predicatelogic (representing a line of code) in this module (representing an operation), generate
    // the TLA+ module and return it in a map indexed by the module name (e.g. pop4)
    public Map<String, String> getModuleNamesAndContent(String abs, InvariantParser invariant, InvariantParser status, 
        String invQ, String statusQ, String D, boolean checkingForNonInterference, Map<String, Type> localVars, String objectName, Formula execQ) {
        Map<String, String> results = new HashMap<String, String>();
        int i=0;
        VariableList allVariables = new VariableList("VARIABLES");
        // Add all the variables required for this module
        for(NameType var: variables.getVariables()) {
            allVariables.addVariable(var.name, var.type);
        }
        // Additional local variables from other operations may be added to the module (so we don't have to parse 
        // the non-interference invariant D which may refer to these), we will need to add these to the UNCHANGED part
        // of the operation, and also initialise them to 0 to avoid increasing the state space
        List<String> newVariables = new ArrayList<String>();
        // Add all local variables again for the new thread
        Iterator<String> it = localVars.keySet().iterator();
        if(checkingForNonInterference) {
            while (it.hasNext()) {
                String localVar = it.next();
                if(!variables.contains(localVar)) {
                    newVariables.add(localVar);
                }
                allVariables.addVariable(localVar, localVars.get(localVar));
                allVariables.addVariable(localVar + syms.Constants.THREAD_SUFFIX, localVars.get(localVar));
            }
        }
        int endPc = 0;
        if(logic.size() > 0) {
            endPc = logic.get(logic.size() - 1).getPc();
        }
        for(Formula pred: logic) {
            String result = new String();
            result += "---------------------------- MODULE " + pred.LHS + (checkingForNonInterference ? syms.Constants.THREAD_MODULE_SUFFIX : "") + "----------------------------\n";
            result += printExtends(extendsModules);
            result += allVariables.printLine(new ArrayList<String>(localVars.keySet()), false);
            result += System.lineSeparator();
            result += System.lineSeparator();
            // Non-interference doesn't affect constants list - they are not thread local
            result += constants.printLine(new ArrayList<String>(localVars.keySet()), false);
            result += System.lineSeparator();
            result += System.lineSeparator();
            String invSection = addPcConstraint(pred.getPc(), invariant.getInvariantForPc(Integer.toString(pred.getPc())));
            int postPc = pred.getPostPc();
            String postInv = invariant.getInvariantForPc(Integer.toString(postPc));
            invSection += System.lineSeparator() + "\t /\\ " + addPcConstraint(postPc, postInv);
            
            Formula inv = new Formula("INV");
            inv.addRHS(invSection);
            
            String statusSection = addPcConstraint(pred.getPc(), status.getInvariantForPc(Integer.toString(pred.getPc())));
            Formula statusPred = new Formula("STATUS");
            statusSection += System.lineSeparator() + "\t /\\ " + addPcConstraint(postPc, status.getInvariantForPc(Integer.toString(postPc)));
            statusPred.addRHS(statusSection);
            
            result += abs;
            result += System.lineSeparator();
            result += System.lineSeparator();
            result += inv.printLine();
            result += System.lineSeparator();
            result += System.lineSeparator();
            result += statusPred.printLine();
            result += System.lineSeparator();
            result += System.lineSeparator();
            if(checkingForNonInterference) {
                result += "D == " + D;
                result += System.lineSeparator();
                result += System.lineSeparator();
                result += "INVq == " + invQ;
                result += System.lineSeparator();
                result += System.lineSeparator();
                result += "STATUSq == " + statusQ;
                result += System.lineSeparator();
                result += System.lineSeparator();
            }
            if(pred.getExec() != null) {
                result += pred.getExec().printLine();
                result += System.lineSeparator();
                result += System.lineSeparator();
                if(checkingForNonInterference) {
                    result += execQ.printLine();
                    result += System.lineSeparator();
                    result += System.lineSeparator();
                }
            }
            if(i < init.size()) {
                Formula init = this.init.get(i);
                String last = init.removeLast();
                for(String var: newVariables) {
                   init.addRHS(var + " = 0 ");
                }
                init.addRHS(last + System.lineSeparator());
                if(checkingForNonInterference) {
                    init.addRHS("pcq \\in 0.." + endPc);
                    init.addRHS("(" + this.getInitForOtherThread(localVars, objectName) + ")");
                }
                result += init.printLine();
                result += System.lineSeparator();
                result += System.lineSeparator();
            }
            this.finaliseUnchanged(pred, new ArrayList<String>(localVars.keySet()), checkingForNonInterference);
            result += pred.printLine();
            result += System.lineSeparator();
            result += System.lineSeparator();
            result += getSpec(pred, allVariables, checkingForNonInterference).printLine();
            result += System.lineSeparator();
            result += System.lineSeparator();
            result += "=============================================================================";
            i++;
            results.put(pred.LHS, result);
        }
        return results;
    }
    /*
     * Generate the 'Init' component for the non-executing thread. This includes a component
     * for all the possible values of the program counter of that thread.
     */
    private String getInitForOtherThread(Map<String, Type> localVars, String objectName) {
        String result = "";
        int i=0;
        for(Formula init: initD) {
            i++;
            Iterator<String> it = localVars.keySet().iterator();
            while(it.hasNext()) {
                String var = it.next();
                String defaultValue = "0";
                Type type = localVars.get(var);
                if(type instanceof Type.ObjectType) {
                    defaultValue = "null";
                } else if (type instanceof Type.IdRefType && 
                        (((Type.IdRefType) type).getName().equals(objectName))) {
                    defaultValue = "null";
                }
                if(!init.printRHS().contains(" " + var + Constants.THREAD_SUFFIX)) {
                    init.addRHS(var + Constants.THREAD_SUFFIX + " = " + defaultValue);
                }
            }
            result += "(" + init.printRHS() + ")";
            if(i < initD.size()) {
                result += System.lineSeparator() + "\\/";
            }
        }
        return result;
    }
    
    /*
     * Generate the 'Init' module used to check the initialisation proof obligation. This is much simpler
     * than the other modules and is independant of the operation, there is only one Init module for an entire algorithm.
     */
    public static String generateInit(String abs, List<String> localVars, Set<String> extendsModules, 
            VariableList allConstants, VariableList allVariables, Formula init) {
        String result = new String();
        result += "---------------------------- MODULE " + syms.Constants.INIT_MODULE_NAME  + "----------------------------\n";
        result += printExtends(extendsModules);
        result += allVariables.printLine(localVars, true);
        result += System.lineSeparator();
        result += System.lineSeparator();
        // Non-interference doesn't affect constants list - they are not thread local
        result += allConstants.printLine(localVars, false);
        result += System.lineSeparator();
        result += System.lineSeparator();
        
        result += abs;
        result += System.lineSeparator();
        result += System.lineSeparator();
        result += "INV == TRUE";
        result += System.lineSeparator();
        result += System.lineSeparator();
        result += "D == TRUE";
        result += System.lineSeparator();
        result += System.lineSeparator();
        result += "INVq == TRUE";
        result += System.lineSeparator();
        result += System.lineSeparator();
        
        result += init.printLine();
        result += System.lineSeparator();
        result += System.lineSeparator();
        
        result += "Stop == FALSE";
        result += System.lineSeparator();
        result += System.lineSeparator();
        Formula spec = new Formula("Spec");
        spec.addRHS("Init");
        spec.addRHS("[][Stop]_" + allVariables.printList(localVars, true));
        result += spec.printLine();
        result += System.lineSeparator();
        result += System.lineSeparator();
        result += "=============================================================================";

        return result;
    }
    
    public void addPredicate(Formula pred) {
        logic.add(pred);
    }
    
    public void setTrueCondition(Formula pred) {
        trueCondition = pred;
    }
    
    public Formula getTrueCondition() {
        return trueCondition;
    }
    
    public void setFalseCondition(Formula pred) {
        falseCondition = pred;
    }
    
    public Formula getFalseCondition() {
        return falseCondition;
    }
    
    /*
     * Merge two modules by combining their logic and variables
     */
    public void append(Module m) {
        if(m != null){
            if(m.logic != null) {
                for(Formula p: m.logic) {
                    this.logic.add(p);
                }
            }
            if(m.variables != null) {
                for(NameType s: m.variables.getVariables()) {
                    this.variables.addVariable(s.name, s.type);
                }
            }
            if(m.variables.instantiation != null) {
                for(String s: m.variables.instantiation.keySet()) {
                    this.variables.instantiation.putIfAbsent(s, m.variables.instantiation.get(s));
                }
            }
        }
    }
    
    /*
     * Gets the 'Spec' temporal formula for TLA+ a module
     */
    private Formula getSpec(Formula pred, VariableList allVariables, boolean checkingForNonInterference) {
        Formula spec = new Formula("Spec");
        spec.addRHS("Init");
        spec.addRHS("[][" + pred.getLHS() + "]_" + allVariables.printList(new ArrayList<String>(), checkingForNonInterference));
        return spec;
    }
    
    /* Get the list of variables which are unchanged by a given predicate, 
     * relies on changed variables being marked using the addChanged method */
    private void finaliseUnchanged(Formula pred, List<String> localVars, boolean checkingForNonInterference) {
        String result = "UNCHANGED<<";
        for(NameType var: variables.getVariables()) {
            pred.addUnchanged(var.name);
        }
        if(checkingForNonInterference) {
            for(String var: localVars) {
                pred.addUnchanged(var);
                pred.addUnchanged(var + Constants.THREAD_SUFFIX);
            }
        }
        for(String var: pred.getUnchanged()) {
            if(!pred.getChanged().contains(var)) {
                result += var;
                result += ",";
            }
        }
        if(!result.equals("UNCHANGED<<")) {
            result = result.substring(0, result.length() -1);
        }
        result += ">>";
        pred.addRHS(result);
    }
}
