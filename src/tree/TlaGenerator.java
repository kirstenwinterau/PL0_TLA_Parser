package tree;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import source.Errors;
import source.Position;
import syms.Constants;
import syms.Predefined;
import syms.SymEntry;
import syms.Type;
import syms.Type.ListType;
import tla.*;
import tla.CompositeStatus.Status;
import tree.ExpNode.NewObjectNode;
import tree.StatementNode.BreakNode;
import tree.StatementNode.CasNode;
import tree.StatementNode.ContinueNode;
import tree.StatementNode.LockNode;
import tree.StatementNode.UnlockNode;
import tree.Tree.*;
import source.Source;

/** 
 * Class TlaGenerator implements TLA+ generation using the
 * visitor pattern to traverse the abstract syntax tree.
 */
public class TlaGenerator implements TreeVisitor, StatementTransform<Module>,
                    ExpTransform<Module> {
    // Module for current procedure 
    private Module module;
    // List of modules for each procedure 
    private List<Module> modules;
    // List of abstract, global and (procedure) local variables
    List<NameType> globalVars = new ArrayList<NameType>();
    List<NameType> abstractVars = new ArrayList<NameType>();
    List<NameType> nonLocalVars = new ArrayList<NameType>();
    Map<String, Type> localVars = new HashMap<String, Type>();
    List<String> localVarDefaults = new ArrayList<String>();
    // Error message handler 
    private Errors errors;
    List<Type> returnTypes = new ArrayList<Type>();
    
    // Whether or not the non-interference component of the modules needs to be generated
    private boolean checkingForNonInterference = true;
    
    // Name of the current procedure we are visiting
    private String currentName = "";
    // True if a linked object structure is present, and our memory model should be used
    private boolean linkedStructure = false;
    // Name of the linked structure if there is one (used to extract abstract variable)
    private String linkedStructureName;
    private Type.ObjectType objectType;
    private String objectName;
    // pc values of linearisation points mapped to TLA+ abstract operations
    private InvariantParser abstractOp;
    // pc values mapped to status (IN, OUT or INOUT) - IDLE status implied for all unspecified pc values
    private InvariantParser status;
    // the Init for the other thread, which will be built up to include cases for all pc values
    private List<Formula> initD;
    // Array of constants/extends modules provided by the user, may be extended to include constants relating to memory model
    private String[] constants;
    private String[] extendsModules;
    // Need to get list of all variables from all operations, to use in Init module and init for other thread
    private Set<NameType> allVariables = new HashSet<NameType>();
    // Whether or not the 'empty' constant was used. We add this in for the user even if they didn't have it in their root module
    private boolean emptyConstantUsed = false;
    // If true, use the encoding that covers potential linearisation points as well as standard ones
    private boolean allowPotentialLinearisationPoints = false;
    // The conditions on status transitions used to generate the logic equivalent to 'exec' for the potential linearisation point encoding
    private Map<String, String> statusTransitions = new HashMap<String, String>();
    // The 'exec' component generated for each value of the program counter, will be combined to generate execQ
    private Map<String, String> execQ = new HashMap<String, String>();
    // List of allowed program counter values (lines in source file that constitute a statement, not necessarily sequential due to whitespace)
    private List<Integer> pcValues;

    public TlaGenerator(Errors errors, Source src, String linkedStructureName, String extendsModules, String constants, InvariantParser abstractOp, InvariantParser status, Map<String, String> statusTransitions, boolean checkingForNonInterference, boolean allowPotentialLinearisationPoints, List<Integer> pcValues) {
        this.errors = errors;
        this.linkedStructure = (!linkedStructureName.isEmpty());
        this.linkedStructureName = linkedStructureName;
        this.abstractOp = abstractOp;
        this.status = status;
        this.checkingForNonInterference = checkingForNonInterference;
        this.initD = new ArrayList<Formula>();
        this.statusTransitions = statusTransitions;
        this.allowPotentialLinearisationPoints = allowPotentialLinearisationPoints;
        this.constants = constants.split(",");
        this.extendsModules = extendsModules.split(",");
        Collections.sort(pcValues);
        this.pcValues = pcValues;
    }

    /*-------------------- Main Method to start TLA+ generation --------*/

    /** Main TLA+ generation for this tree. */
    public List<Module> generateTla( ProgramNode node ) {
        modules = new ArrayList<Module>();
        module = new Module();
        localVars.put("pc", new Type.NullType());
        localVars.put("in", new Type.NullType());
        localVars.put("out", new Type.NullType());
        this.visitProgramNode( node );
        String localString = new String();
        for(int i=0; i< localVars.size(); i++) {
            localString = localString + localVars.get(i) + ", ";
        }

        if(checkingForNonInterference) {
            for(Module module: modules) {
                allVariables.addAll(module.variables.getVariables());
                module.setInitD(initD);
            }
        }
        return modules;
    }
    
    /* -------------------- Visitor methods ----------------------------*/
    
    /** Generate the code for the main program. */
    public void visitProgramNode( ProgramNode node ) {
        node.getBlock().accept( this );
    }

    /** Generate TLA+ for a block. */
    public void visitBlockNode( BlockNode node ) {
        module.append( node.getBody().genCode( this ) );
        node.getProcedures().accept(this);
    }

    /** Generate TLA+ for a declaration list */
    public void visitDeclListNode( DeclNode.DeclListNode node ) {
        for( DeclNode decl : node.getDeclarations() ) {
            decl.accept( this );
        }
    }
    
    /** Generate TLA+ for a procedure node */
    public void visitProcedureNode( DeclNode.ProcedureNode node ) {
        returnTypes = node.getProcEntry().getReturnTypes();
        module = new Module();
        for(NameType global : nonLocalVars) {
            module.variables.addVariable(global.name, global.type);
        }
        addModelVariables(linkedStructure);
        
        // Get the name of the operation, which is used to name modules
        currentName = node.getProcEntry().getIdent();
        ExpNode.ArgumentsNode args = (ExpNode.ArgumentsNode) node.getProcEntry().getArgs();
        
        // Add predicate that acts as the entry point of the operation
        Formula invoke = new Formula(currentName + "0");
        invoke.constrainPc(0, getNextPc(node.getInitPc()));

        // If the operation has an arguments, it is assigned to 'in' and its type is constrained
        if(args.getArgs().size() > 1 || !(args.getArgs().get(0) instanceof ExpNode.EmptyNode) ) {
            List<Type> types = new ArrayList<Type>();
            int i=1;
            for(ExpNode arg : args.getArgs()) {
                Type type = arg.getType();
                String exp = arg.toString();
                types.add(type);
                localVars.put(exp,  type);
                if(args.getArgs().size() == 1) {
                    invoke.addRHS(exp + "' \\in " + type.toString());
                    invoke.addRHS("in' = " + exp + "'");
                }
                else {
                    invoke.addRHS("in'[" + i + "] = " + exp + "'");
                }
                invoke.addChanged(exp);
                module.variables.addInstantiation(exp, node.getInitPc());
                i++;
            }
            module.variables.addVariable("in", new Type.ListType(types));
            if(args.getArgs().size() != 1) {
                invoke.addRHS("in' \\in " + new Type.ListType(types).toString());
            }
            invoke.addChanged("in");
            updateUnchanged(invoke);
        }
        module.addPredicate(invoke);
        
        // Add any arguments to the function as variables in the module
        for(ExpNode arg: args.getArgs()) {
            if(!(arg instanceof ExpNode.EmptyNode)) module.variables.addVariable(arg.toString(), arg.getType());
        }
        
        // Visit the body of the procedure
        node.getBlock().accept( this );
        
        // Loop over the predicates and add the appropriate abstract operation components or 
        // other constraints from exec
        for(Formula pred: module.getPredicateList()) {
            handleAopAndExec(pred);
            Formula init = new Formula("Init");
            generateInit(init, pred);
        }
        finaliseProcedure(module);
        modules.add(module);
    }
    
    private void generateInit(Formula init, Formula pred) {
        Formula initOtherThread = new Formula("initDSection");
        initOtherThread.addRHS("pc" + syms.Constants.THREAD_SUFFIX + " = " + pred.getPc());
        boolean absAdded = false;
        boolean invAdded = false;
        // Sort the variables into non-local variables, then local variables, then in/out.
        // We add the non-locals then ABS, then locals then INV then in/out then STATUS to Init
        // for added efficiency when running the model checker
        for(NameType var : module.variables.getSortedVariablesForInit(new ArrayList<NameType>(nonLocalVars))) {
            if(!nonLocalVars.contains(var) && !var.name.equals("mem") && !absAdded) {
                init.addRHS("ABS");
                absAdded = true;
            }
            if((var.name.equals("in") || var.name.equals("out")) && !invAdded) {
                init.addRHS("INV");
                initOtherThread.addRHS("INVq");
                initOtherThread.addRHS("D");
                invAdded = true;
            }
            addVariableToInit(var, init, initOtherThread, pred.getPc(), 
                    module.variables.instantiatedAt(var.name, pred.getPc()),
                    module.variables.stronglyInstantiatedAt(var.name, pred.getPc()), false);
        }
        // Make sure we have added ABS, INV etc due to edge cases e.g. if there are no local variables
        addRemainingInvariants(checkingForNonInterference, init, initOtherThread, absAdded, invAdded);
        if(checkingForNonInterference) {
            // Don't add initD segment for both true and false cases of a line, initial states are the same
            if(!pred.getLHS().endsWith(Constants.FALSE_SUFFIX)) {
                initD.add(initOtherThread);
            }
        }
        module.addInit(init);
        updateConstants(module);
    }
    
    /*
     * Because of the way we add invariants to Init as we finish adding certain sets of variables (for
     * efficiency), there are certain cases where they don't get added (for example, if neither 'in'
     * or 'out' are present as variables, then we never detect that we have finished adding local
     * variables, so never add "INV". We ensure here that all the invariants have been added.
     */
    private void addRemainingInvariants(boolean checkingForNonInterference, Formula init, Formula initOtherThread, boolean absAdded, boolean invAdded) {
        if(!absAdded) {
            init.addRHS("ABS");
        }
        if(!invAdded) {
            init.addRHS("INV");
            if(checkingForNonInterference) {
                init.addRHS("INVq");
                init.addRHS("D");
            }
        }
        // STATUS is never added until the end, no need to check if it was already added
        init.addRHS("STATUS");
        if(checkingForNonInterference) {
            initOtherThread.addRHS("STATUSq");
        }
    }
    
    private void handleAopAndExec(Formula pred) {
        List<Status> startStatuses = parseStatusList(status.getInvariantForPc(Integer.toString(pred.getPc())));
        List<Status> postStatuses = parseStatusList(status.getInvariantForPc(Integer.toString(pred.getPostPc())));
        // Abstract op may only occur in true/false case (for example, if the LP is a CAS oepration), for
        // this reason we might have T/F specific cases in the abstract operation (e.g. pc = 5T => ...)
        String pcWithSuffix = Integer.toString(pred.getPc());
        if(pred.getLHS().endsWith(Constants.TRUE_SUFFIX)) {
            pcWithSuffix += "." + Constants.TRUE_SUFFIX;
        } else if (pred.getLHS().endsWith(Constants.FALSE_SUFFIX)) {
            pcWithSuffix += "." + Constants.FALSE_SUFFIX;
        }
        String abstractOpSegment = abstractOp.getInvariantForPc(pcWithSuffix);
        // If there wasn't an AOP specific to a the pc with suffix, try the raw pc
        if(abstractOpSegment.equals("TRUE")) {
            abstractOpSegment = abstractOp.getInvariantForPc(Integer.toString(pred.getPc()));
        }
        String abstractStateUnchanged = generateAbstractVarsUnchangedConstraint();
        String inUnchanged = module.variables.contains("in") ? "in' = in" : null;
        String outUnchanged = module.variables.contains("out") ? "out' = out" : null;
        
        // Standard linearisation points only - if there is an AOP segment for this pc value, add it to the next-state relation
        if(!allowPotentialLinearisationPoints) {
            if(abstractOpSegment != "TRUE") {
                pred.addRHS(abstractOpSegment);
                updateChangedForAop(pred, abstractOpSegment, checkingForNonInterference);
            }
            return;
        }
        
        // Don't have abstract variable in UNCHANGED<<>>, we will constrain it in exec
        List<String> changedVars = updateChangedForAop(pred, abstractOpSegment, checkingForNonInterference);
        // In branches of exec where we don't perform an AOP, we need to specify  these as unchanged
        String unchangedIfNoAop = "UNCHANGED<<";
        for(String var: changedVars) {
            unchangedIfNoAop += var + ",";
        }
        if(!changedVars.isEmpty()) {
            unchangedIfNoAop = unchangedIfNoAop.substring(0, unchangedIfNoAop.length() - 1);
        }
        unchangedIfNoAop += ">>";
        
        // Always add the components of exec for changes in status, including the conditions
        // given by the user for each of these transitions to occur. Because we have the conditions
        // from the user, this component of exec will always evaluate to false if the transition is not allowed
        Formula exec = new Formula("Exec");
        Formula execOtherThread = new Formula("ExecQ");
        exec.setSeparator(System.lineSeparator() + "\t \\/");
        for(String transition: Arrays.asList(Constants.STATUS_TRANSITIONS)) {
            String condition = statusTransitions.get(transition);
            CompositeStatus status = parseCompositeStatusFromHelperName(transition);
            String component = getExecLogicForTransition(status, condition, abstractOpSegment, abstractStateUnchanged, inUnchanged, outUnchanged, unchangedIfNoAop);
            exec.addRHS(component);
            execOtherThread.addRHS(component);
        }
        
        // For transitions where status stays the same, include all such transitions from the start statuses
        // of this line in execQ (in execQ, pc is not changing). For normal exec, only include them if the status
        // is in both the start statuses and the post statuses.
        for(Status status: startStatuses) {
            String component = getExecLogicForTransition(new CompositeStatus(status, status), null, abstractOpSegment, abstractStateUnchanged, inUnchanged, outUnchanged, unchangedIfNoAop);
            if(postStatuses.contains(status)) {
                exec.addRHS(component);
            }
            execOtherThread.addRHS(component);
        }
        pred.addRHS("Exec");
        // If applicable, add component to ExecQ, using 'pc=x => ...' format
        if(checkingForNonInterference) {
            pred.addRHS("ExecQ");
            execQ.put(Integer.toString(pred.getPc()), execOtherThread.printRHS());
        }
        pred.setExec(exec);
    }
    
    /*
     * Given a string containing a list of statuses, assumed to be separated by
     * ors, returns the list of possible statuses
     */
    private List<Status> parseStatusList(String list) {
        List<Status> statuses = new ArrayList<Status>();
        if(list.matches(Constants.IN_REGEX)) {
            statuses.add(Status.In);
        }
        if(list.matches(Constants.INOUT_REGEX)) {
            statuses.add(Status.Inout);
        }
        if(list.matches(Constants.OUT_REGEX)) {
           statuses.add(Status.Out);
        }
        return statuses;
    }
    
    /*
     * Given the name of a helper-definition, used to define the conditions under which
     * status transitions can occur, return the composite status that represents this transition
     */
    private CompositeStatus parseCompositeStatusFromHelperName(String helperName) {
        if(helperName.equals("IN_OUT")) { 
            return new CompositeStatus(Status.In, Status.Out);
        } else if (helperName.equals("IN_INOUT")) {
            return new CompositeStatus(Status.In, Status.Inout);
        } else if (helperName.equals("INOUT_OUT")) {
            return new CompositeStatus(Status.Inout, Status.Out);
        } else if (helperName.equals("INOUT_IN")) {
            return new CompositeStatus(Status.Inout, Status.In);
        }
        return new CompositeStatus(Status.Idle, Status.Idle);
    }
    
    /*
     * Puts together the component of 'exec' for a given status transition
     */
    private String getExecLogicForTransition(CompositeStatus status, String condition, String abstractOp, String abstractStateUnchanged, String inUnchanged, String outUnchanged, String unchangedIfNoAop) {
        Formula pred = new Formula("Exec");
        // We have a user-defined condition for when the status transition can 
        // occur, add this as a conjunction to the exec component
        if(condition != null) {
            pred.addRHS("(" + condition.trim() + ")");
        }
        if(status.pre == Status.In && status.post == Status.Out) {
            pred.addRHS(abstractOp);
        } else if (status.pre == Status.In && status.post == Status.Inout) {
            pred.addRHS(abstractOp);
            pred.addRHS(inUnchanged);
            pred.addRHS(abstractStateUnchanged);
        } else if (status.pre == Status.Inout && status.post == Status.Out) {
            String out = outUnchanged == null ? "TRUE" : outUnchanged;
            String unchanged = "(" + abstractStateUnchanged + " /\\ " + out +" /\\ " + unchangedIfNoAop + ")";
            pred.addRHS("(" + "(" + abstractOp + ")" + " \\/ " + unchanged + ")");
        } else if (status.pre == Status.Inout && status.post == Status.Inout) {
            pred.addRHS(abstractStateUnchanged);
            pred.addRHS(inUnchanged);
            String out = outUnchanged == null ? "TRUE" : outUnchanged;
            pred.addRHS("("  + "(" + abstractOp + ")" + " \\/ " +  "(" + out + " /\\ " + unchangedIfNoAop + ")" + ")");
        } else if (status.pre == Status.In && status.post == Status.In) {
            pred.addRHS(abstractStateUnchanged);
            pred.addRHS(inUnchanged);
            pred.addRHS(unchangedIfNoAop);
        } else if (status.pre == Status.Inout && status.post == Status.In) {
            pred.addRHS(abstractStateUnchanged);
            pred.addRHS(inUnchanged);
            pred.addRHS(unchangedIfNoAop);
        } else if (status.pre == Status.Out && status.post == Status.Out) {
            pred.addRHS(abstractStateUnchanged);
            pred.addRHS(outUnchanged);
            pred.addRHS(unchangedIfNoAop);
        }
        return "(" + pred.printRHS().trim() + ")";
    }
    
    /*
     * Check an abstract operation for any variables it changes. This doesn't parse
     * the TLA+ but simply scans for the presence of primed abstract variables.
     */
    private List<String> updateChangedForAop(Formula pred, String abstractOp, boolean checkingForNonInterference) {
        List<String> changedVars = new ArrayList<String>();
        if(abstractOp == null) return changedVars;
        // Check for changes to abstract variables
        for(NameType var: abstractVars) {
            if(abstractOp.contains(var.name + "'")) {
                if(!pred.getChanged().contains(var.name))
                    changedVars.add(var.name);
                pred.addChanged(var.name);
            }
        }
        // Check for changes to 'in'
        if(abstractOp.contains("in'")) {
            if(!pred.getChanged().contains("in"))
                changedVars.add("in");
            pred.addChanged("in");
            if(checkingForNonInterference)
                pred.addChanged("in" + Constants.THREAD_SUFFIX);
        }
        // Check for changes to 'out'
        if(abstractOp.contains("out'")) {
            if(!pred.getChanged().contains("out"))
                changedVars.add("out");
            pred.addChanged("out");
            if(checkingForNonInterference)
                pred.addChanged("out" + Constants.THREAD_SUFFIX);
            module.variables.addInstantiation("out", pred.getPc() + 1);
        }
        return changedVars;
    }
    
    /*
     * Generated an 'UNCHANGED<<>>' list including all abstract variables,
     * used in exec when we need to specify as' = as 
     */
    private String generateAbstractVarsUnchangedConstraint() {
        if(abstractVars.size() == 0) return null;
        String result = "UNCHANGED<<";
        int i=0;
        for(NameType var: abstractVars) {
            i++;
            result += (var.name);
            if(i != abstractVars.size()) {
                result += ",";
            }
        }
        result += ">>";
        return result;
    }
    
    /*
     * Ensure that the last line of the procedure returns the program counter to 0, 
     * reflecting that the program returns to IDLE state
     */
    private void finaliseProcedure(Module module) {
        Formula pred = module.getPredicateList().get(module.getPredicateList().size() -1);
        if(pred.isEmptyLoop()) return;
        pred.constrainPc(pred.getPc(), 0);
        if(pred.getLHS().endsWith(Constants.TRUE_SUFFIX) || pred.getLHS().endsWith(Constants.FALSE_SUFFIX)) {
            pred = module.getPredicateList().get(module.getPredicateList().size() - 2);
            pred.constrainPc(pred.getPc(), 0);
        }
    }
    
    /*
     * Check if the 'empty' constant is used, and if so automatically add it
     * to the constants list
     */
    private void updateConstants(Module module) {
        if(emptyConstantUsed) {
            module.constants.addVariable(Constants.EMPTY_CONSTANT, new Type.NullType());
        }
    }
    
    
    /** Generate TLA+ for a variable list node */
    public void visitVarListNode( DeclNode.VarListNode node ) {
        List<String> vars = node.getVars();
        List<Type> types = node.getTypes();
        // Determine if the variable is abstract, global or local and add 
        // it to the appropriate list
        List<Boolean> isGlobal = node.getGlobalIndicators();
        List<Boolean> isAbstract = node.getAbstractIndicators();
        for(int i=0; i< vars.size(); i++) {
            if(isGlobal.get(i)) {
                globalVars.add(new NameType(vars.get(i).toString(), types.get(i)));
                nonLocalVars.add(new NameType(vars.get(i).toString(), types.get(i)));
            } else if (isAbstract.get(i)) {
                abstractVars.add(new NameType(vars.get(i).toString(), types.get(i)));
                nonLocalVars.add(new NameType(vars.get(i).toString(), types.get(i)));
            } else {
                localVars.put(vars.get(i), types.get(i));
            }
        }
    }
    
    /*
     * Creates the 'Init' definition for the 'Init.tla' module
     */
    public Formula getInitModule() {
        Formula init = new Formula("Init");
        Formula initD = new Formula("InitD");
        initD.addRHS("pcq = 0");
        for(NameType var: allVariables) {
            // Don't want in/out in Init module
            if(!var.name.equals("in") && !var.name.equals("out")) {
                addVariableToInit(var, init, initD, -1, false, false, true);
            }
        }
        // Initialise linked structure as empty
        if(!linkedStructureName.isEmpty()) {
            init.addRHS("Len(" + linkedStructureName + ") = 0");
        }
        init.addRHS("(" + initD.printRHS() + ")");
        return init;
    }
    
    /** Add generic variables (such as program counter) and any required for the 
     * memory model to the module */
    private void addModelVariables(boolean linkedStructure) {
        for(String moduleName: extendsModules) {
            if(moduleName.equals("Status")) continue;
            module.extendsModule(moduleName.trim());
        }
        for(String constant: constants) {
            module.constants.addVariable(constant.trim(), new Type.NullType());
        }
        module.variables.addVariable("pc", Predefined.INTEGER_TYPE);
        if(!linkedStructure) return;
        module.extendsModule(Constants.SEQUENCE_FILE_NAME);
        module.variables.addVariable(linkedStructureName, new Type.NullType());
        module.variables.addVariable("mem", new Type.NullType());
        module.constants.addVariable("Ref", new Type.NullType());
        module.constants.addVariable("null", new Type.NullType());
        module.constants.addVariable("N", new Type.NullType());
        module.constants.addVariable("undef", new Type.NullType());
        
        // Remove any constants that were mistaken as variables when parsing variable declaration list
        Iterator<String> iter = localVars.keySet().iterator();
        while (iter.hasNext()) {
            String var = iter.next();
            if (module.constants.contains(var)) {
                iter.remove();
            }
        }
    }
    
    /**
     * Add constraints for a given variable into the Init predicate, based
     * on its type and whether or not it has been instantiated (for objects)
     */
    private void addVariableToInit(NameType var, Formula init, Formula initD, int currentPc, boolean isInstantiated, boolean isStronglyInstantiated, boolean initModule) {
        Type type = var.type;
        // Dereference a reference type
        if(type instanceof Type.ReferenceType) {
            Type.ReferenceType refType = (Type.ReferenceType) var.type;
            type = refType.getBaseType();
        }
        if(var.name != null && var.name.equals("pc")) {
            init.addRHS(var.name + " = " + Math.max(0, currentPc));
        // It is assumed that 'in' and 'out' may have only simple types (can't be objects), since
        // they are part of the abstract operation and abstract state
        //TODO: Future work - Are there situations where we should instantiate out, or can it always be default (e.g. 0)?
        } else if (var.name.equals("out")) {
            Type.ListType listType = (Type.ListType) var.type;
            if(listType.getTypes().size() == 1) {
                init.addRHS(var.name + " = 0");
                initD.addRHS(var.name + Constants.THREAD_SUFFIX  + " = 0");
            } else {
                init.addRHS(var.name  + " \\in " + listType.toString());
                initD.addRHS(var.name  + Constants.THREAD_SUFFIX + " \\in " + listType.toString());
                for(int i=0; i< listType.getTypes().size(); i++) {
                    init.addRHS(var.name + "[" + (i+1) + "] = 0");
                    initD.addRHS(var.name + Constants.THREAD_SUFFIX + "[" + i + "] = 0");
                }
            }
        } else if (var.name.equals("in")) {
            if(currentPc != 0) {
                init.addRHS(var.name + " \\in " + var.type.toString());
                initD.addRHS(var.name + Constants.THREAD_SUFFIX + " \\in " + var.type.toString());
            } else {
                Type.ListType listType = (Type.ListType) var.type;
                if(listType.getTypes().size() == 1) {
                    init.addRHS(var.name + " = 0");
                    initD.addRHS(var.name + Constants.THREAD_SUFFIX  + " = 0");
                } else {
                	init.addRHS(var.name  + " \\in " + listType.toString());
                    initD.addRHS(var.name  + Constants.THREAD_SUFFIX + " \\in " + listType.toString());
                    for(int i=0; i< listType.getTypes().size(); i++) {
                        init.addRHS(var.name + "[" + (i+1) + "] = 0");
                        initD.addRHS(var.name + Constants.THREAD_SUFFIX + "[" + i + "] = 0");
                    }
                }
            }
        // Initial value of 'mem' is built up based on the object used for the linked list and its fields
        } else if(var.name.equals("mem")) {
            String typeString = "";
            // 'Init.tla' module, can set all memory references to point to undef
            if(currentPc == -1) {
                typeString = "{undef}";
            } else {
                typeString = "(";
                List<Type> types = objectType.getVariables().getTypes();
                for(Type t : types) {
                   if(t instanceof Type.ObjectType || 
                           t instanceof Type.IdRefType && 
                           (((Type.IdRefType) t).getName().equals(objectName))) {
                       typeString += "(Ref \\union {null})";
                   } else {
                       typeString += t.toString();
                   }
                   typeString += " \\X ";
                }
                typeString = typeString.substring(0, typeString.length() - 4);
                typeString += ") \\union {undef}";
            }
            init.addRHS("mem \\in [Ref ->" + typeString + "]");
        // Abstract variable representing linked list
        } else if (var.name.equals(linkedStructureName)) {
            init.addRHS(var.name + " \\in FiniteSeq(T, N)");
            if(!nonLocalVars.contains(new NameType(var.name, type)))
                initD.addRHS(var.name + " \\in FiniteSeq(T, N)");
        // Variable has an object type
        } else if(type instanceof Type.ObjectType || type instanceof Type.ReferenceType && (((Type.IdRefType) type).getName().equals(objectName)) ) {
            boolean finished = false;
            for(NameType global : nonLocalVars) {
                if(global.name.equals(var.name) && !initModule) {
                    init.addRHS(var.name + " \\in Ref \\union {null}");
                    finished = true;
                }
            }
            if (finished) {
                ;
            } else if (isStronglyInstantiated) {
                init.addRHS(var.name + " \\in Ref");
                if(!nonLocalVars.contains(new NameType(var.name, type)))
                    initD.addRHS(var.name + syms.Constants.THREAD_SUFFIX + " \\in Ref");
            } else if(isInstantiated || (nonLocalVars.contains(new NameType(var.name, type)) && !initModule)) {
                init.addRHS(var.name + " \\in Ref \\union {null}");
                if(!nonLocalVars.contains(new NameType(var.name, type)))
                    initD.addRHS(var.name + syms.Constants.THREAD_SUFFIX + " \\in Ref \\union {null}");
            } else {
                init.addRHS(var.name + " = null");
                if(!nonLocalVars.contains(new NameType(var.name, type)))
                    initD.addRHS(var.name + syms.Constants.THREAD_SUFFIX + " = null");
            }
        // Special case for 'lock' variable, representing a memory lock
        } else if (type instanceof Type.LockType) {
            init.addRHS(var.name + " \\in {TRUE, FALSE}");
        // Variable is a generic type 
        } else {
            module.constants.addVariable(type.toString(), new Type.GenericType(type.toString()));
            if(isInstantiated || (nonLocalVars.contains(new NameType(var.name, type)) && !initModule)) {
                init.addRHS(var.name + " \\in " + type.toString());
                if(!nonLocalVars.contains(new NameType(var.name, type))) {
                    initD.addRHS(var.name + syms.Constants.THREAD_SUFFIX + " \\in " + type.toString());
                }
            } else {
                init.addRHS(var.name + " = 0");
                if(!nonLocalVars.contains(new NameType(var.name, type))) {
                    initD.addRHS(var.name + syms.Constants.THREAD_SUFFIX + " = 0");
                }
            }
        }
    }
    
    /*************************************************
     *  Statement node code generation visit methods
     *************************************************/
    /** Code generation for an erroneous statement should not be attempted. */
    public Module visitStatementErrorNode( StatementNode.ErrorNode node ) {
        errors.fatal( "PL0 Internal error: generate TLA for Statement Error Node",
                node.getPosition() );
        return new Module();
    }
    
    /*
     * Get the value of the program counter for the statement that immediately follows the
     * statement with the given program counter value
     */
    private int getNextPc(int pc) {
        // Check current pc is in our list of allowed pc values, and is not the last value
        // If not, we do our best guess and add 1
        if(pcValues.indexOf(pc) == -1 || 
                pcValues.indexOf(pc) >= pcValues.size() - 1) {
            return pc + 1;
        }
        // Return the next value in the list of allowed pc values
        return pcValues.get(pcValues.indexOf(pc) + 1);
    }

    /** Code generation for an assignment statement. */
    public Module visitAssignmentNode(StatementNode.AssignmentNode node) {
        Module tla = new Module();
        String name = currentName +node.getPc();
        Formula predicate = new Formula(name);
        predicate.constrainPc(node.getPc(), getNextPc(node.getPc()));
        ExpNode.VariableNode variable = (ExpNode.VariableNode) node.getVariable();
        
        // Variable being assigned to is instantiated after this line (need this info for Init)
        String[] nameSegments = variable.getName().split(".");
        String varName = nameSegments.length > 0 ? nameSegments[0] : variable.getName();
        module.variables.addInstantiation(varName, node.getPc() + 1);
        if(!module.constants.contains(variable.getVariable().getIdent())) {
            module.variables.addVariable(variable.getVariable().getIdent(), variable.getType());
        }
        
        if(variable.getVariable().getType().getBaseType() instanceof Type.ObjectType) {
            objectType = (Type.ObjectType) variable.getVariable().getType().getBaseType();
            objectName = objectType.getName();
        }
        
        // RHS is an object
        if(node.getExp() instanceof ExpNode.NewObjectNode) {
            processAssignmentOfObject(module, predicate, variable, (ExpNode.NewObjectNode) node.getExp(), 
                    node.getPc(), node.getPosition());
            updateChanged(predicate, node.getVariable());
        // LHS is not an object attribute and RHS is a variable
        } else if(!variable.isObjectAttribute() && (node.getExp() instanceof ExpNode.VariableNode)) {
            processAssignmentOfVariable(module, predicate, variable, (ExpNode.VariableNode) node.getExp());
            updateChanged(predicate, node.getVariable());
        // LHS is not an object attribute and RHS is a dereferenced variable
        } else if(!variable.isObjectAttribute() && (node.getExp() instanceof ExpNode.DereferenceNode)) {
            processAssignmentOfDereferencedVariable(module, predicate,
                    variable, (ExpNode.DereferenceNode) node.getExp());
            updateChanged(predicate, node.getVariable());
        // LHS is an object attribute
        } else if (variable.isObjectAttribute()) {
            processAssignmentToObjectAttribute(predicate, variable, node.getExp());
        // Default basic case
        } else {
            Module exp = node.getExp().genCode(this);
            predicate.addRHS(node.getVariable().toString() + "' = " + exp.getTrueCondition().getLHS());
            updateChanged(predicate, node.getVariable());
        }
        updateUnchanged(predicate);
        tla.addPredicate(predicate);
        return tla;
    }

    private void processAssignmentToObjectAttribute( Formula predicate,
            ExpNode.VariableNode variable, ExpNode exp) {
        int index = variable.getIndex();
        String objectName = variable.getVariable().getIdent();
        String tuple = "";
        // Find the index of the variable being changed in the ordered list of object attributes
        for(int i=0; i<variable.getTupleLength(); i++) {
            if(i == index) {
                tuple = tuple.concat(exp.toString());
            } else {
                tuple = tuple.concat("@[" + (i + 1) + "]");
            }
            tuple = tuple.concat(",");
        }
        tuple = tuple.substring(0, tuple.length() -1);
        predicate.addRHS("mem' = [mem EXCEPT ![" + objectName + "] = <<" + tuple + ">>]");
        predicate.addChanged("mem");
    }

    private void processAssignmentOfDereferencedVariable(Module module,
            Formula predicate, ExpNode.VariableNode variable, ExpNode.DereferenceNode expressionRef) {
        ExpNode.VariableNode expression = (ExpNode.VariableNode) expressionRef.getLeftValue();
        // RHS is an object attribute
        if(expression.isObjectAttribute()) {
            predicate.addRHS(variable.toString() + "' = mem" + 
                    "[" + expression.getVariable().getIdent() + "][" + (expression.getIndex() + 1) +  "]");
        // Most simple case
        } else {
            predicate.addRHS(variable.toString() + "' = " + expression.getVariable().getIdent());
        }
    }

    private void processAssignmentOfVariable(Module module, Formula predicate, 
            ExpNode.VariableNode variable, ExpNode.VariableNode expression) {
        // RHS is an object attribute
        if(expression.isObjectAttribute()) {
            predicate.addRHS(variable.toString() + "' = mem" + 
                    "[" + expression.getVariable().getIdent() + "][" + (expression.getIndex() + 1) +  "]");
        // Most simple case
        } else {
            predicate.addRHS(variable.toString() + "' = " + expression.toString());
        }
    }

    private void processAssignmentOfObject(
            Module module, Formula predicate, ExpNode.VariableNode variable, ExpNode.NewObjectNode exp, int pc, Position pos) {
        module.variables.addStrongInstantiation(variable.getName(), pc);
        Type.ObjectType object = (Type.ObjectType) exp.getType();
        objectType = object;
        objectName = object.getName();
        // Assigning an object to a variable, after this it will point to a reference in memory (won't be null)
        predicate.addRHS(variable.getName() + "' \\in Ref");
        int index = -1;
        DeclNode.VarListNode vars = object.getVariables();
        int i=0;
        String rhs = new String();
        // Generate a list of default values for each object attribute
        for(Type type : vars.getTypes()) {
            i++;
            Type baseType = Type.ERROR_TYPE;
            if(type instanceof Type.IdRefType) {
                Type.IdRefType refType = (Type.IdRefType) type;
                baseType = refType.resolveType(pos);
            }
            if(baseType instanceof Type.ObjectType) {
                index = i;
                rhs = rhs.concat("null");
            } else if (type instanceof Type.ObjectType) {
                index = i;
                rhs = rhs.concat("null");
            } else {
                rhs = rhs.concat("0");
            }
            rhs = rhs.concat(",");
        }
        String name = variable.toString();
        predicate.addRHS("(\\A r\\in Ref : mem[r][" + index + "] /= " + name + "' /\\ (mem[r] /= undef => r /= " + name + "'))");
        rhs = rhs.length() > 0 ? rhs.substring(0, rhs.length() -1) : rhs;
        predicate.addRHS("mem'= [mem EXCEPT ![" + variable + "'] = <<" + rhs + ">>]");
        predicate.addChanged("mem");
    }
    
    /*
     * Given the identifier of a variable that gets changed by a transition relation, update the
     * transition relation so that this variable will not be included in the UNCHANGED<<>> list
     */
    private static void updateChanged(Formula predicate, ExpNode identifier) {
        if(!(identifier instanceof ExpNode.VariableNode)) return;
        ExpNode.VariableNode var = (ExpNode.VariableNode) identifier;
        String name = var.getVariable().getIdent();
        // Assigning to object attribute results in root object being changed (e.g. a.b = c, want to say 'a' is changed)
        String[] parts = name.split("\\.");
        predicate.addChanged(parts[0]);
    }
    
    /*
     * Add all variables to the UNCHANGED<<>> list for a transition relation. We will later
     * remove any that get explicitly changed.
     */
    private void updateUnchanged(Formula predicate) {
        for(NameType var: module.variables.getVariables()) {
            String[] parts = var.name.split("\\.");
            predicate.addUnchanged(parts[0]);
        }
    }
    
    /** Generate TLA+ for a "write" statement. */
    public Module visitWriteNode( StatementNode.WriteNode node ) {
        // Write nodes not used
        return new Module();
    }
    
    /** Generate TLA+ for a "call" statement. */
    public Module visitCallNode( StatementNode.CallNode node ) {
        //TODO: Future work - Allow procedures to be called
        Module module = new Module();
        return module;
    }
    
    /** Generate TLA+ for a statement list */
    public Module visitStatementListNode( StatementNode.ListNode node ) {
        Module tla = new Module();
        // Visit statements one by one
        for( StatementNode s : node.getStatements() ) {
            if(s == null) continue;
            tla.append( s.genCode( this ) );
        }
        return tla;
    }

    /** Generate TLA+ for an "if" statement. */
    public Module visitIfNode(StatementNode.IfNode node) {
        // Generate the true condition
        Module condition = node.getCondition().genCode(this);
        Formula conditionTrue = new Formula(currentName + node.getPc() + Constants.TRUE_SUFFIX);
        conditionTrue.constrainPc(node.getPc(), node.getThenStmt().getPc());
        conditionTrue.addRHS(condition.getTrueCondition().getLHS());
        processCas(conditionTrue, node.getCondition());
        
        // Generate the false condition
        Formula conditionFalse = new Formula(currentName + node.getPc() + Constants.FALSE_SUFFIX);
        conditionFalse.constrainPc(node.getPc(), getNextPc(node.getElseStmt().getPc()));
        conditionFalse.addRHS(condition.getFalseCondition().getLHS());
        
        Module tla = new Module();
        updateUnchanged(conditionTrue);
        updateUnchanged(conditionFalse);
        tla.addPredicate(conditionTrue);
        tla.addPredicate(conditionFalse);
        
        // Generate the body of the branches
        Module thenTla = node.getThenStmt().genCode(this);
        Module elseTla = node.getElseStmt().genCode(this);
        tla.append(thenTla);
        tla.append(elseTla);
        return tla;
    }
    
    /** Generate TLA+ for a "CAS" statement. */
    public Module visitCasNode(CasNode node) {
        Module oldValue = node.getOldValue().genCode(this);
        Module compareValue = node.getCompareValue().genCode(this);
        Module newValue = node.getNewValue().genCode(this);
        
        // Generate the condition in the true case
        Formula conditionTrue = new Formula(currentName + node.getPc() + Constants.TRUE_SUFFIX);
        conditionTrue.constrainPc(node.getPc(), getNextPc(node.getPc()));
        conditionTrue.addRHS(oldValue.getTrueCondition().getLHS() + " = " + 
                compareValue.getTrueCondition().getLHS());
        // Include the assignment component 
        conditionTrue.addRHS(oldValue.getTrueCondition().getLHS() + "' = " + 
                newValue.getTrueCondition().getLHS());
        conditionTrue.addChanged(oldValue.getTrueCondition().getLHS());
        
        // From the assignment part of a CAS, a variable will be instantiated
        String[] nameParts = oldValue.getTrueCondition().getLHS().split(".");
        String name = nameParts.length > 0 ? nameParts[0] : oldValue.getTrueCondition().getLHS();
        module.variables.addInstantiation(name, node.getPc() + 1);
        
        // Generate the alse condition
        Formula conditionFalse = new Formula(currentName + node.getPc() + Constants.FALSE_SUFFIX);
        conditionFalse.constrainPc(node.getPc(), getNextPc(node.getPc()));
        conditionFalse.addRHS(oldValue.getTrueCondition().getLHS() + " /= " + 
                compareValue.getTrueCondition().getLHS());
        
        Module tla = new Module();
        updateUnchanged(conditionTrue);
        updateUnchanged(conditionFalse);
        tla.addPredicate(conditionTrue);
        tla.addPredicate(conditionFalse);
        return tla;
    }
 
    /** Generate TLA+ for a "while" statement. */
    public Module visitWhileNode(StatementNode.WhileNode node) {
        // Capture variables that are already instantiated
        Set<String> currentInstantiations = module.variables.getInstantiations().keySet();
        Module condition = node.getCondition().genCode(this);
        
        // Generate the true and false conditions
        Formula conditionTrue = new Formula(currentName + node.getPc() + Constants.TRUE_SUFFIX);
        conditionTrue.constrainPc(node.getPc(), getNextPc(node.getPc()));
        Formula trueCondition = condition.getTrueCondition();
        Formula conditionFalse = new Formula(currentName + node.getPc() + Constants.FALSE_SUFFIX);

        // Not a while(true), in which case we ignore the while(true) line and don't generate a module 
        // for it as an optimisation
        if(!trueCondition.getLHS().equals(Constants.TRUE_CONSTANT)) {
            conditionTrue.addRHS(condition.getTrueCondition().getLHS());
            processCas(conditionTrue, node.getCondition());
            conditionFalse.constrainPc(node.getPc(), node.getEndPc());
            conditionFalse.addRHS(condition.getFalseCondition().getLHS());
        }
        
        Module tla = new Module();
        // Again, make sure this is not a while(true)
        if(!trueCondition.getLHS().equals(Constants.TRUE_CONSTANT)) {
            updateUnchanged(conditionTrue);
            updateUnchanged(conditionFalse);
            tla.addPredicate(conditionTrue);
            tla.addPredicate(conditionFalse);
        }
        
        // Handle the loop body
        Module bodyTla = node.getLoopStmt().genCode( this );
        
        boolean finished = false;
        // Ensure that the last statement in the loop returns to the top of the loop as a default
        for(Formula p: bodyTla.getPredicateList()) {
            if(p.getPostPc() == node.getEndPc() && !p.isBreakStatement()) {
                p.constrainPc(p.getPc(), getNextPc(node.getPc()));
                finished = true;
            }
        }
        if(!finished && bodyTla.getPredicateList().size() != 0) {
            Formula p = bodyTla.getPredicateList().get(bodyTla.getPredicateList().size() - 1);
            p.constrainPc(p.getPc(), getNextPc(node.getPc()));
        }
        // If we have an empty while loop, don't change pc in the true case
        if(bodyTla.getPredicateList().size() == 0) {
            conditionTrue.constrainPc(conditionTrue.getPc(), conditionTrue.getPc());
            conditionTrue.flagAsEmptyLoop();
            conditionFalse.flagAsEmptyLoop();
        }
        
        tla.append( bodyTla );
        
        // Update any variables that were intialised during the loop to
        // be initialised at the beginning of the loop
        updateLoopInstantiations(currentInstantiations, node.getPc());
        return tla;
    }
    
    /** Generate the TLA+ for a "repeat-until" statement. */
    public Module visitRepeatNode(StatementNode.RepeatUntilNode node) {
        // Capture variables that are already initialsed
        Set<String> currentInstantiations = module.variables.getInstantiations().keySet();
        Module tla = node.getLoopStmt().genCode(this);
        
        // Generate true condition
        Module condition = node.getCondition().genCode(this);
        Formula lastTrue = new Formula(currentName + node.getEndPc() + Constants.TRUE_SUFFIX);
        lastTrue.constrainPc(node.getEndPc(), getNextPc(node.getEndPc()));
        lastTrue.addRHS(condition.getTrueCondition().getLHS());
        processCas(lastTrue, node.getCondition());
        
        // Generate false condition
        Formula lastFalse = new Formula(currentName + node.getEndPc() + Constants.FALSE_SUFFIX);
        lastFalse.constrainPc(node.getEndPc(), node.getLoopStmt().getPc());
        lastFalse.addRHS(condition.getFalseCondition().getLHS());
        
        updateUnchanged(lastTrue);
        updateUnchanged(lastFalse);
        tla.addPredicate(lastTrue);
        tla.addPredicate(lastFalse);
        
        // Update any variables that were intialised during the loop to
        // be initialised at the beginning of the loop
        updateLoopInstantiations(currentInstantiations, node.getPc());
        return tla;
    }
    
    /** Generate the TLA+ for a "do-while" statement. */
    public Module visitDoWhileNode(StatementNode.DoWhileNode node) {
        // Capture variables that are already initialsed
        Set<String> currentInstantiations = module.variables.getInstantiations().keySet();
        
        // Handle the loop body
        Module tla = node.getLoopStmt().genCode(this);
        
        // Generate the true condition
        Module condition = node.getCondition().genCode(this);
        Formula lastTrue = new Formula(currentName + node.getEndPc() + Constants.TRUE_SUFFIX);
        lastTrue.addRHS(condition.getTrueCondition().getLHS());
        lastTrue.constrainPc(node.getEndPc(), node.getLoopStmt().getPc());
        processCas(lastTrue, node.getCondition());
        
        // Generate the false condiiton
        Formula lastFalse = new Formula(currentName + node.getEndPc() + Constants.FALSE_SUFFIX);
        lastFalse.constrainPc(node.getEndPc(), getNextPc(node.getEndPc()));
        lastFalse.addRHS(condition.getFalseCondition().getLHS());
        
        updateUnchanged(lastTrue);
        updateUnchanged(lastFalse);
        tla.addPredicate(lastTrue);
        tla.addPredicate(lastFalse);
        
         // Update any variables that were intialised during the loop to
        // be initialised at the beginning of the loop
        updateLoopInstantiations(currentInstantiations, node.getPc());
        return tla;
    }
    
    /**
     * Mark any objects which are allocated within a loop as being potentially
     * allocated from the beginning of the loop onwards
     */
    private void updateLoopInstantiations(Set<String> oldKeys, int pc) {
        Set<String> newKeys = module.variables.getInstantiations().keySet();
        if(newKeys.size() == oldKeys.size()) return;
        for(String key: newKeys) {
            if(!oldKeys.contains(key)) {
                module.variables.updateInstantiation(key, pc);
            }
        }
    }
    
    private void processCasInternal(Formula predicate, ExpNode.CasNode condition) {
        ExpNode.VariableNode variable = (ExpNode.VariableNode) condition.getArgs().getArgs().get(0);
        ExpNode exp = condition.getArgs().getArgs().get(2);
        // Variable being assigned to is instantiated after this line (need this info for Init)
        String[] nameSegments = variable.getName().split(".");
        String varName = nameSegments.length > 0 ? nameSegments[0] : variable.getName();
        module.variables.addInstantiation(varName, predicate.getPc() + 1);
        if(!module.constants.contains(variable.getVariable().getIdent())) {
            module.variables.addVariable(variable.getVariable().getIdent(), variable.getType());
        }
        
        if(variable.getVariable().getType().getBaseType() instanceof Type.ObjectType) {
            objectType = (Type.ObjectType) variable.getVariable().getType().getBaseType();
            objectName = objectType.getName();
        }
        
        // RHS is an object
        if(exp instanceof ExpNode.NewObjectNode) {
            processAssignmentOfObject(module, predicate, variable, (ExpNode.NewObjectNode) exp, 
                    predicate.getPc(), condition.getPosition());
            updateChanged(predicate, variable);
        // LHS is not an object attribute and RHS is a variable
        } else if(!variable.isObjectAttribute() && (exp instanceof ExpNode.VariableNode)) {
            processAssignmentOfVariable(module, predicate, variable, (ExpNode.VariableNode) exp);
            updateChanged(predicate, variable);
        // LHS is not an object attribute and RHS is a dereferenced variable
        } else if(!variable.isObjectAttribute() && (exp instanceof ExpNode.DereferenceNode)) {
            processAssignmentOfDereferencedVariable(module, predicate,
                    variable, (ExpNode.DereferenceNode) exp);
            updateChanged(predicate, variable);
        // LHS is an object attribute
        } else if (variable.isObjectAttribute()) {
            processAssignmentToObjectAttribute(predicate, variable, exp);
        // Default basic case
        } else {
            predicate.addRHS(variable.toString() + "' = " + exp.toString());
            updateChanged(predicate, variable);
        }
        updateUnchanged(predicate);
    }
    
    /**
     * Generate the TLA+ for the assignment component of a CAS operation,
     * for the true case only
     */
    private void processCas(Formula trueCase, ExpNode condition) {
        // Not a CAS condition, no extra work required
        if(!(condition instanceof ExpNode.CasNode)) return;
        processCasInternal(trueCase, (ExpNode.CasNode) condition);
    }
    
    /**
     * Generate the TLA+ for a break statement
     */
    public Module visitBreakNode(BreakNode node) {
    	Module tla = new Module();
        Formula p = new Formula(currentName + node.getPc());
        // Exit the loop
        p.constrainPc(node.getPc(), getEndPcFromLoopStatement(node.getEnclosingLoop()));
        p.flagAsBreakStatement();
        tla.addPredicate(p);
        return tla;
    }

    /** 
     * Generate the TLA+ for a continue statement
     */
    public Module visitContinueNode(ContinueNode node) {
        Module tla = new Module();
        Formula p = new Formula(currentName + node.getPc());
        // Return to the beginning of the loop
        p.constrainPc(node.getPc(), getStartPcFromLoopStatement(node.getEnclosingLoop()));
        tla.addPredicate(p);
        return tla;
    }
    /**
     * Get the program counter corresponding to the first line of code in the loop, 
     * depending on the type of loop
     */
    private int getStartPcFromLoopStatement(StatementNode loopStatement) {
        if (loopStatement instanceof StatementNode.WhileNode) {
            StatementNode.WhileNode node = (StatementNode.WhileNode) loopStatement;
            return node.getPc();
        } else if (loopStatement instanceof StatementNode.RepeatUntilNode) {
            StatementNode.RepeatUntilNode node = (StatementNode.RepeatUntilNode) loopStatement;
            return node.getPc();
        }
        return -1;
    }
    /**
     * Get the program counter corresponding to the line of code after a loop ends, 
     * depending on the type of loop
     */
    private int getEndPcFromLoopStatement(StatementNode loopStatement) {
        if (loopStatement instanceof StatementNode.WhileNode) {
            StatementNode.WhileNode node = (StatementNode.WhileNode) loopStatement;
            return node.getEndPc();
        } else if (loopStatement instanceof StatementNode.RepeatUntilNode) {
            StatementNode.RepeatUntilNode node = (StatementNode.RepeatUntilNode) loopStatement;
            return getNextPc(node.getEndPc());
        }
        return -1;
    }
    
    /**
     * Generate the TLA+ for a return statement of a procedure
     */
    public Module visitReturnNode(StatementNode.ReturnNode node) {
        Module tla = new Module();
        Formula p = new Formula(currentName + node.getPc());
        // Program returns to IDLE state, pc becomes 0
        p.constrainPc(node.getPc(), 0);
        // If we are returning something, we need 'out' variable
        if(!node.isEmpty()) {
            module.variables.addVariable("out", new Type.ListType(returnTypes));
        }
        updateUnchanged(p);
        tla.addPredicate(p);
        return tla;
    }
    
    /*************************************************
     *  Expression node code generation visit methods
     *************************************************/
    /** Code generation for an erroneous expression should not be attempted. */
    public Module visitErrorExpNode( ExpNode.ErrorNode node ) { 
        errors.fatal( "PL0 Internal error: generateCode for ErrorExpNode",
                node.getPosition() );
        return new Module();
    }

    /** Generate TLA+ for a constant expression. */
    public Module visitConstNode( ExpNode.ConstNode node ) {
        Module module = new Module();
        module.setTrueCondition(new Formula(Integer.toString(node.getValue())));
        module.setFalseCondition(new Formula(Integer.toString(node.getValue())));
        return module;
    }

    /** Generate TLA+ for a "read" expression. */
    public Module visitReadNode( ExpNode.ReadNode node ) {
        // Read nodes not used
        return new Module();
    }
    
    /** Generate TLA+ for a binary expression. */
    public Module visitOperatorNode( ExpNode.OperatorNode node ) {
        ExpNode.ArgumentsNode argNode = (ExpNode.ArgumentsNode) node.getArg();
        List<ExpNode> args = argNode.getArgs();
        // Generate TLA for given operator and opposite (e.g. = and /=), for if
        // this operation is part of a condition and we generate true and false cases
        String trueOperator = getTlaForOp(node.getOp(), false);
        String falseOperator = getTlaForOp(node.getOp(), true);
        Module module = new Module();
        //TODO: Future work - Handle non-binary operators
        Module lhs = args.get(0).genCode(this);
        Module rhs = args.get(1).genCode(this);
        module.setTrueCondition(new Formula(lhs.getTrueCondition().getLHS() + " " +  trueOperator + " " +  rhs.getTrueCondition().getLHS()));
        module.setFalseCondition(new Formula(lhs.getTrueCondition().getLHS() + " " +  falseOperator + " " +  rhs.getTrueCondition().getLHS()));
        return module;
    }
    /** Generate code for condition in a a CAS expression */
    public Module visitCasNode( ExpNode.CasNode node ) {
        ExpNode.ArgumentsNode argNode = (ExpNode.ArgumentsNode) node.getArgs();
        List<ExpNode> args = argNode.getArgs();
        Module module = new Module();
        // Conditions when the entire CAS statement evaluates to true/false
        module.setTrueCondition(new Formula(getTlaForIdentifier(args.get(0).toString()) + " " +  "=" + " " +  getTlaForIdentifier(args.get(1).toString())));
        module.setFalseCondition(new Formula(getTlaForIdentifier(args.get(0).toString()) + " " +  "/=" + " " +  getTlaForIdentifier(args.get(1).toString())));
        return module;
    }
    
    /*
     * Get the TLA for a variable identifier to be used on the RHS of an assignment, 
     * for accessing an object attribute (e.g. a.b) we need an expression of the
     * form mem[x][y], otherwise the identifier is left unchanged
     */
    private String getTlaForIdentifier(String identifier) {
        if(!identifier.contains(".")) {
            return identifier;
        }
        //TODO: Future work - Allow chaining of accesses to object attributes
        String[] parts = identifier.split("\\.");
        List<String> attributes = objectType.getVariables().getVars();
        for(int i=0; i<attributes.size(); i++) {
            if(attributes.get(i).equals(parts[1])) {
                return "mem[" + parts[0] +"][" + (i + 1) + "]";
            }
        }
        return "mem[" + parts[0] +"][ERROR]";
    }
    
    /** Get the TLA+ representation of an operator, optionally its inverse/negation */
    private static String getTlaForOp(Operator op, boolean negate) {
        //TODO: Future work - Support more operators
        if(op.name().equals("EQUALS_OP")) {
            return negate ? "/=" : "=";
        } else if(op.name().equals("NEQUALS_OP")){
            return negate ? "=" : "/=";
        } else if(op.name().equals("LESS_OP")){
            return negate ? ">=" : "<";
        } else if(op.name().equals("LEQUALS_OP")){
            return negate ? ">" : "<=";
        } else if(op.name().equals("GREATER_OP")){
            return negate ? "<=" : ">";
        } else if(op.name().equals("GEQUALS_OP")){
            return negate ? "<" : ">=";
        } else if(op.name().equals("MOD_OP")){
            return "%";
        } else if(op.name().equals("ADD_OP")) {
            return "+";
        } else if(op.name().equals("SUB_OP")) {
            return "-";
        }
        else return "Error";
    }

    /** Generate the code to load arguments (in order) */
    public Module visitArgumentsNode( ExpNode.ArgumentsNode node ) {
        return new Module();
    }

    /** Generate TLA+ to dereference an RValue. */
    public Module visitDereferenceNode( ExpNode.DereferenceNode node ) {
        ExpNode lval = node.getLeftValue();
        Module tla = lval.genCode( this );
        return tla;
    }

    /** Generate TLA+ for an identifier. */
    public Module visitIdentifierNode(ExpNode.IdentifierNode node) {
        /** Visit the corresponding constant or variable node. */
        Module module = new Module();
        // Return the variable and also the variable negated, for use in !(x) conditions
        module.setTrueCondition(new Formula(getTlaForIdentifier(node.getId())));
        module.setFalseCondition(new Formula("!" + node.getId()));
        // Add variable to variable list (unless it is a constant)
        if(!module.constants.contains(node.getId())) {
            this.module.variables.addVariable(node.getId(), node.getType());
        }
        return module;
    }
    
    /** Generate TLA+ for a variable (Exp) reference. */
    public Module visitVariableNode( ExpNode.VariableNode node ) {
        SymEntry.VarEntry var = node.getVariable();
        Module module = new Module();
        // Return the variable and also the variable negated, for use in !(x) conditions
        module.setTrueCondition(new Formula(getTlaForIdentifier(node.getName())));
        module.setFalseCondition(new Formula("!" + node.getName()));
        // Add variable to variable list (unless it is a constant)
        if(!this.module.constants.contains(var.getIdent())) {
            this.module.variables.addVariable(var.getIdent(), var.getType());
        }
        // Keep track of whether 'empty' constant is used, we add this automatically
        // for the user to the list of constants (so they can use it even if they 
        // forget to add it to the constants list in the user input module)
        if(var.getIdent().equals(Constants.EMPTY_CONSTANT)) {
            emptyConstantUsed = true;
        }
        return module;
    }
    
    /** Generate TLA+ to perform a bounds check on a subrange. */
    public Module visitNarrowSubrangeNode(ExpNode.NarrowSubrangeNode node) {
        return new Module();
    }

    /** Generate TLA+ to widen a subrange to an integer. */
    public Module visitWidenSubrangeNode(ExpNode.WidenSubrangeNode node) {
        return new Module();
    }

    /** Generate the TLA+ for the generation of a new object */
    public Module visitNewObjectNode(NewObjectNode node) {
        return new Module();
    }

    /** Generate the TLA+ for a call to lock() */
    public Module visitLockNode(LockNode node) {
        // Add the global lock variable to the procedure if it is not already there
        addLockVariable();
        Module tla = new Module();
        Formula p = new Formula(currentName + node.getPc());
        // To lock the memory, we require it is currently unlocked 
        p.addRHS("lock = FALSE");
        // Lock the memory
        p.addRHS("lock' = TRUE");
        p.addChanged("lock");
        p.constrainPc(node.getPc(), getNextPc(node.getPc()));
        tla.addPredicate(p);
        return tla;
    }

    /** Generate the TLA+ for a call to unlock() */
    public Module visitUnlockNode(UnlockNode node) {
        // Add the global lock variable to the procedure if it is not already there
        addLockVariable();
        Module tla = new Module();
        Formula p = new Formula(currentName + node.getPc());
        // Unlock the memory
        p.addRHS("lock = TRUE");
        p.addRHS("lock' = FALSE");
        p.addChanged("lock");
        p.constrainPc(node.getPc(), getNextPc(node.getPc()));
        tla.addPredicate(p);
        return tla;
    }
    
    /** Add a variable to represent a lock on some segment of memory, used 
     * by lock() and unlock() functions */
    private void addLockVariable() {
        module.variables.addVariable("lock", new Type.LockType());
        globalVars.add(new NameType("lock", new Type.LockType()));
        nonLocalVars.add(new NameType("lock", new Type.LockType()));
    }
    
    /** Get the name of the object type if there is one */
    public String getObjectName() {
        return objectName;
    }
    
    /** Get the list of procedure local variables */
    public Map<String, Type> getLocalVars() {
        return localVars;
    }
    
    /** Get the value of execQ (conjoined exec values for each pcq) */
    public Formula getExecQ() {
        Formula result = new Formula("ExecQ");
        result.setSeparator(System.lineSeparator() + "\t/\\");
        Iterator<String> iterator = execQ.keySet().iterator();
        // Build up execQ in 'pc=x => (...)' format
        while(iterator.hasNext()) {
            String pc = iterator.next();
            String exec = execQ.get(pc);
            String execForQ = InvariantParser.getInvariantForOtherThread(new ArrayList<String>(localVars.keySet()), exec);
            execForQ = "(pcq = " + pc + "  => " + execForQ + ")";
            result.addRHS(execForQ);
        }
        return result;
    }

}
