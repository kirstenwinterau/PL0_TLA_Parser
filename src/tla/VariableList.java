package tla;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.HashSet;
import syms.Type;
/*
 * Represents a list of variables (or constants) in a TLA+ module, ends up
 * being VARIABLE a, b, c or CONSTANT a, b, c in the TLA+ module
 */
public class VariableList {
    // name of the variable list (i.e. VARIABLE or CONSTANT) 
    protected String type;
    protected Set<String> variableNames;
    protected Set<NameType> variables;
    // Object may still be null
    protected HashMap<String, Integer> instantiation;
    // Know that the object is not null (e.g. n = new Node())
    protected HashMap<String, Integer> strongInstantiation;
    
    public VariableList(String type) {
        this.type = type;
        variables = new HashSet<NameType>();
        instantiation = new HashMap<String, Integer>();
        strongInstantiation = new HashMap<String, Integer>();
        variableNames = new HashSet<String>();
    }
    public void addInstantiation(String name, int pc) {
        instantiation.putIfAbsent(name, pc);
    }
    public void addStrongInstantiation(String name, int pc) {
        strongInstantiation.putIfAbsent(name, pc);
    }
    public void updateInstantiation(String name, int pc) {
        instantiation.put(name, pc);
    }
    public boolean contains(String name) {
        return variableNames.contains(name);
    }
    public int getInstantiation(String name) {
        return instantiation.get(name);
    }
    public boolean stronglyInstantiatedAt(String name, int pc) {
        if(strongInstantiation.get(name) == null) {
            return false;
        }
        return strongInstantiation.get(name) <= pc;
    }
    public boolean instantiatedAt(String name, int pc) {
        if(instantiation.get(name) == null) {
            return false;
        }
        return instantiation.get(name) <= pc;
    }
    /***
     * Adds a variable to the list, if it isn't already there
     * @param name The name of the variable
     * @param type The type of the variable
     * @return True if the variable is successfully added, false if a variable of
     * that name was already in the list (it doesn't get added)
     */
    public boolean addVariable(String name, Type type) {
        if(this.type.equals("VARIABLE") && name.equals("null")) return false;
        if(!variableNames.contains(name)) {
            variableNames.add(name);
            variables.add(new NameType(name, type));
            return true;
        }
        return false;
    }
    
    public HashMap<String, Integer> getInstantiations() {
        return new HashMap<String, Integer>(instantiation);
    }
    
    public void removeVariable(String name) {
        variables.remove(name);
    }
    public Set<NameType> getVariables() {
        return this.variables;
    }
    public List<NameType> getSortedVariablesForInit(List<NameType> nonLocalVars) {
        Set<NameType> unorderedVars = new HashSet<NameType>(variables);
        List<NameType> orderedVars = new ArrayList<NameType>();
        // mem is a special case of a non-local variable that is not part of the PL/0 code
        nonLocalVars.add(new NameType("mem", new Type.NullType()));
        // Put the non-local (global and abstract) variables first
        for(NameType var: nonLocalVars) {
            if(unorderedVars.contains(var)) {
                orderedVars.add(var);
                unorderedVars.remove(var);
            }
        }
        // Use iterator to avoid concurrent modification exceptions when deleting a we go
        Iterator<NameType> unorderedVarsIterator = unorderedVars.iterator();
        // Put local vars next (all other variables which are not 'in' or 'out')
        while (unorderedVarsIterator.hasNext()) {
            NameType var = unorderedVarsIterator.next();
            if(var.name.equals("in") || var.name.equals("out")) continue;
            orderedVars.add(var);
            unorderedVarsIterator.remove();
        }
        unorderedVarsIterator = unorderedVars.iterator();
        // Put status-related variables last
        while(unorderedVarsIterator.hasNext()) {
            NameType var = unorderedVarsIterator.next();
            orderedVars.add(var);
            unorderedVarsIterator.remove();
        }
        assert(unorderedVars.isEmpty());
        return orderedVars;
    }
    
    /*
     * Used for debugging, to check that variables are being set as 'instantiated' at the 
     * correct point. We keep track of variable instantiation so that we can reduce the 
     * initial state space to a default value of the variable if it is not instantiated (e.g.
     * null or 0)
     */
    public void printInstantiation() {
        for(String s : instantiation.keySet()) {
            System.out.println(s + ", " + instantiation.get(s));
        }
    }
    /*
     * Prints the type (VARIABLE, CONSTANT) followed by the list of variables, suitable
     * for direct insertion into a TLA+ module
     */
    public String printLine(List<String> localVars, boolean checkingForNonInterference) {
        String result = new String();
        result += type;
        result += " ";
        Iterator<NameType> iter = variables.iterator();
        while (iter.hasNext()) {
            NameType var = iter.next();
            result += var.name;
            result += ",";
            result += " ";
            if(checkingForNonInterference && localVars.contains(var.name)) {
                result += var.name + syms.Constants.THREAD_SUFFIX;
                result += ",";
                result += " ";
            }
        }
        if(variables.size() >= 1) {
            result = result.substring(0, result.length() -2);
        }
        
        return result;
    }
    /*
     * Prints the lis of variables without the name (e.g. a, b, c rather than VARIABLE a, b, c)
     */
    public String printList(List<String> localVars, boolean checkingForNonInterference) {
        String result = "<<";
        Iterator<NameType> iter = variables.iterator();
        while(iter.hasNext()) {
            NameType var = iter.next();
            result += var.name;
            result += ", ";
            if(checkingForNonInterference && localVars.contains(var.name)) {
                result += var.name + syms.Constants.THREAD_SUFFIX;
                result += ",";
                result += " ";
            }
        }
        if(result.length() >= 2) {
            result = result.substring(0, result.length() -2);
        }
        result += ">>";
        return result;
    }
}
