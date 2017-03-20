package pl0;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import parser.LexicalToken;
import parser.Parser;
import parser.Scanner;
import parser.TokenStream;
import source.ErrorHandler;
import source.Errors;
import source.Position;
import source.Source;
import syms.Constants;
import tla.InvariantParser;
import tla.Module;
import tla.NameType;
import tla.Formula;
import tla.VariableList;
import tree.TlaGenerator;
import tree.StaticChecker;
import tree.Tree;
import tree.Tree.ProgramNode;

/** 
 * class PL0-RD - PL0 Compiler with recursive descent parser.
 * @version $Revision: 22 $  $Date: 2014-05-20 15:14:36 +1000 (Tue, 20 May 2014) $
 * Parses the command line arguments, and then compiles and/or executes the
 * code.
 */
public class PL0_RD {

    /** Output stream for compiler */
    public static PrintStream outStream = System.out;
    /** Output stream for error messages */
    public static PrintStream errStream = System.err;
    /** Print usage information */
    public static void usage() {
        outStream.println(
            "PL0 Compiler\n" +
            "Usage: java pl0.PL0_RD [-pt] <pl0> \n"+
            "  -p  =  parse only\n" +
            "  -t  = test mode, save output files to separate 'test-output' directory \n" + 
            " <pl0> PL/0 algorithm to be compiled (must have .pl0 file extension) \n" +
            " The TLA+ inputs must be in a file with the same name & directory but a .tla extension \n");
    }
    /** Suffix expected for pl0 files */
    public static String SourceSuffix = ".pl0";
    /** Suffix expected for TLA+ files */
    public static String TlaSuffix = ".tla";
    /** Save files in 'test-output' sub-directory rather than same directory as input files */
    private static boolean testMode = false;

    /** PL0 main procedure */
    public static void main( String args[] ) throws java.lang.Exception {
        /** Name of the file containing the PL/0 algorithm. */
        String srcFile = null;
        /** Name of the file containing the TLA+ invariants. */
        String tlaFile = null;
        /** Error handler for reporting error messages */
        Errors errors;
        /** PL/0 input source stream */
        Source src;
        /** TLA+ file stream */
        FileReader tla;
        /** Generate the TLA+ files or just parse and static check */
        boolean compile = true;

        /* Parse command line */
        for( String arg : args ) {
            if( arg.charAt(0) == '-' ) { /* Option */
                switch( arg.charAt(1) ) {
                case 'p': /* Parse only */
                    compile = false;
                    break;
                case 't': /* Test mode */
                    testMode = true;
                    break;
                case 'h': /* Help */
                default:
                    usage();
                    System.exit(0);
                    break;
                }
            } else { /* ( arg.charAt(0) != '-' ) Not Option */
                if(srcFile == null) {
                    srcFile = arg;
                    // File path passed in with percentage sin place of spaces, reverse this
                    srcFile = srcFile.replace("%", " ");
                    tlaFile = srcFile.replace(SourceSuffix, TlaSuffix);
                }
            }
        }
        try {
            /* Set up the input source stream for the source file and TLA invariant file */
            if( srcFile == null ) {
                errStream.println( "No PL/0 source file specified." );
                System.exit( 1 );
            }
            src = new Source( srcFile );
            tla = new FileReader( tlaFile );
            /* Set up the error handler reference */
            errors = new ErrorHandler( errStream, src );
            /* Compile the program */
            compile( src, tla, tlaFile, errors, compile );
        } catch( IOException e ) {
            System.out.println( "Got IOException: " + e + "... Aborting" );
            System.exit(1);
        }
    }

    /** Compile the program
     * 
     * @param src program source
     * @param tla TLA invariants
     * @param rootFilePath file path to the root module of the TLA+ spec we are generating for
     * @param errors handler for errors
     * @param compile generate TLA+ modules or just do parse and static check
     */
    private static List<Module> compile( Source src, FileReader tlaFile, String rootFilePath, Errors errors, boolean compile ) 
        throws IOException, Exception
    {
        /** Abstract syntax tree returned by parser */
        Tree.ProgramNode tree = null;
        /** Generated code for procedures */
        List<Module> tla = new ArrayList<Module>();
        /** Abstract syntax tree returned by parser */
        Tree.ProgramNode parseResult; 
        /** Name of the linked structure (FiniteSeq) in the specification if there is one */
        String linkedStructureName = "";
        /** List of allowed pc values in the algorithm (corresponding to lines in source code file) */
        List<Integer> pcValues = null;
        /** If potential linearization points are allowed, we use more complex encoding approach. The new
         *  encoding is backwards compatible, but the old way is more readable so we keep it as an option */
        boolean allowPotentialLinearisationPoints = false;
        
        outStream.println( "Compiling " + src.getFileName() );
        try {
            /* Set up the lexical analyzer using the source program stream */
            Scanner lex = new Scanner( src );
            /* Record the input source for lexical tokens */
            LexicalToken.setSource( src );
            /** Recursive descent parser.
             * Set up the parser with the lexical analyzer. We
             * choose not to use debug parse as errors are printed
             * to user in GUI and we don't want the amount of
             * errors to be overwhelming */
            TokenStream tokens = new TokenStream( lex, false );
            Parser parser = new Parser( tokens, src.getLinePositions() );
            parseResult = parser.parse();
            linkedStructureName = parser.getLinkedStructureName();
            pcValues = parser.getPcValues();
            Tree.ProgramNode parseTree = (Tree.ProgramNode) parseResult;
            if(parseTree != null) {
                outStream.println(parseTree.toString());
            }
            /* Flush any error messages from the parse */
            errors.flush();
            outStream.println( "Parsing complete" );
            if( parseResult instanceof Tree.ProgramNode ) {
                tree = (Tree.ProgramNode)parseResult;
                /* Perform the static semantics analysis */
                StaticChecker staticSemantics = 
                    new StaticChecker( ErrorHandler.getErrorHandler() );
                staticSemantics.visitProgramNode( tree );           
                /* Don't generate any TLA if there are any errors. */
                if( ErrorHandler.getErrorHandler().hadErrors() ) {
                    /* Skip TLA generation if there were errors */
                    tree = null;
                }
                errors.flush();
                outStream.println( "Static semantic analysis complete" );
            }
        } catch (IOException e) {
            System.err.println( "Exception: " + e + "... Aborting" );
            System.exit(1);
        }
        if( tree != null && compile ) {
            Map<String, String> invariants = InvariantParser.parseInvariantsFromFile(tlaFile, (ErrorHandler) errors);
            
            // If the user has specified any of the status transitions, we assume they want potential linearisation point mode
            for(String transition: Arrays.asList(Constants.STATUS_TRANSITIONS)) {
                if(!invariants.get(transition).trim().equals("FALSE")) {
                    allowPotentialLinearisationPoints = true;
                }
            }
            String rawInvariant = invariants.get("INV");
            String rawStatus = invariants.get("STATUS");
            String rawAbstractOp = invariants.get("AOP");
            String abs = invariants.get("ABS");
            String rawStatusHelper = invariants.get("STATUSHELPER");
            
            /* Parse the invariants */
            InvariantParser statusHelper = new InvariantParser(rawStatusHelper);
            InvariantParser invariant = new InvariantParser(rawInvariant);
            InvariantParser status = new InvariantParser(rawStatus);
            InvariantParser abstractOp = new InvariantParser(rawAbstractOp);
            
            File rootModuleFile = new File(rootFilePath);
            String rootPath = rootModuleFile.getParent();
            
            // Save output to 'test-output' directory so don't clutter 'test-pgm' folder
            if(testMode) {
                rootPath = rootPath.concat("/test-output");
            }

            List<String> generatedModuleNames = new ArrayList<String>();
            /* Generate the TLA+ modules for both simulation and non-interference */
            generatedModuleNames.addAll(generateAndSaveModules(false, allowPotentialLinearisationPoints, 
                    errors, src, tree, linkedStructureName, pcValues, abstractOp, abs, status, statusHelper, 
                    invariant, invariants, rootPath));
            generatedModuleNames.addAll(generateAndSaveModules(true, allowPotentialLinearisationPoints, 
                    errors, src, tree, linkedStructureName, pcValues, abstractOp, abs, status, statusHelper, 
                    invariant, invariants, rootPath));

            generatedModuleNames.add(Constants.INIT_MODULE_NAME);
            saveGeneratedModuleNames(generatedModuleNames, rootPath, (ErrorHandler) errors);
            
        }
        errors.flush();
        errors.errorSummary();
        return tla;
    }
    
    /*
     * Generates the TLA+ module for each line of code and saves them to output files in the same directory
     * as the PL/0 file
     */
    private static List<String> generateAndSaveModules(boolean checkingForNonInterference, boolean allowPotentialLinearisationPoints, Errors errors, Source src, ProgramNode tree, 
            String linkedStructureName, List<Integer> pcValues, InvariantParser abstractOp, String abs, InvariantParser status, InvariantParser statusHelper, 
            InvariantParser invariant, Map<String, String> invariants, String rootPath) {
        String constants = invariants.get("CONSTANT");
        String extendsModules = invariants.get("EXTENDS");
        
        if(constants == null) constants = "";
        TlaGenerator tlaGen = new TlaGenerator( errors, src, linkedStructureName, extendsModules, constants, abstractOp, statusHelper, invariants, checkingForNonInterference, allowPotentialLinearisationPoints, pcValues);
        List<Module> tla = tlaGen.generateTla( tree );
        outStream.println( "TLA+ generation complete" );
        
        // Generate the versions of INV and STATUS for the other thread
        String invQ = InvariantParser.getInvariantForOtherThread(new ArrayList<String>(tlaGen.getLocalVars().keySet()), invariant.getRawInvariant());
        String statusQ = InvariantParser.getInvariantForOtherThread(new ArrayList<String>(tlaGen.getLocalVars().keySet()), status.getRawInvariant());
        
        // We keep track of the names of the generated modules, so we can save a list in a file as a log
        List<String> generatedModuleNames = new ArrayList<String>();
        
        Set<String> allExtends = new HashSet<String>();
        // All constants used across all operations. Whilst the compiler only
        // adds the constants used by the operation the line of code is in, we
        // need all modules to include all constants due to the approach in the
        // GUI which uses the same TLA+ model for all modules
        VariableList allConstants = new VariableList("CONSTANTS");
        // Variables for the init module, excludes in and out
        VariableList initVariables = new VariableList("VARIABLES");
        
        for(Module module : tla) {
            allExtends.addAll(module.getExtendsModules());
            for(NameType constant: module.constants.getVariables()) {
                allConstants.addVariable(constant.name, constant.type);
            }
            for(NameType variable : module.variables.getVariables()) {
                // Don't want in/out in Init module, these are procedure-local
                if(!variable.name.equals("in") && !variable.name.equals("out")) {
                    initVariables.addVariable(variable.name, variable.type);
                }
            }
        }
        
        // Save the modules for each line of code and print them to stdout for debugging
        for(Module module : tla) {
            Map<String, String> namesAndContents = module.getModuleNamesAndContent(abs, invariant, status, invQ, statusQ, invariants.get("D"), 
                    checkingForNonInterference, tlaGen.getLocalVars(), tlaGen.getObjectName(), tlaGen.getExecQ());
            for(String name: namesAndContents.keySet()) {
                outStream.println(name);
                outStream.println();
                outStream.println(namesAndContents.get(name));
                outStream.println();
            }
            for(String name: namesAndContents.keySet()) {
                saveModule(name, namesAndContents.get(name), rootPath, checkingForNonInterference, (ErrorHandler) errors);
                generatedModuleNames.add(name + (checkingForNonInterference ? Constants.THREAD_MODULE_SUFFIX : ""));
            }
        }
        
        // Also save the 'Init' module
        Formula init = tlaGen.getInitModule();
        String initContents = Module.generateInit(abs, new ArrayList<String>(tlaGen.getLocalVars().keySet()), allExtends, allConstants, initVariables, init);
        saveModule(Constants.INIT_MODULE_NAME, initContents, rootPath, false, (ErrorHandler) errors);
        
        return generatedModuleNames;
    }
    
    /*
     * Saves the list of names of each of the generated modules. This can be used by an external program
     * to easily collect them all and show them to the user, for example.
     */
    private static void saveGeneratedModuleNames(List<String> names, String rootPath, ErrorHandler errors) {
        String filePath = rootPath + "/moduleGenInfo.txt";
        File file = new File(filePath);
        BufferedWriter writer = null;
        try {
            writer = new BufferedWriter(new FileWriter(file, false));
            for(String name: names) {
                writer.write(name);
                writer.write(System.lineSeparator());
            }
            writer.flush();
        } catch (IOException e) {
            errors.fatal("Could not save information about generated modules in ModuleGenInfo.txt", new Position(0));
            System.exit(1);
            e.printStackTrace();
        } finally {
            if(writer != null) {
                try {
                    writer.close();
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        }
    }
    
    /*
     * Saves a given module in the same directory as the .pl0 and .tla inputs. For a module used to check simulation,
     * the file is given the same name as the module, with a .tla extension. If this is a module used to check 
     * non-interference, we add and suffix to the module name.
     */
    private static void saveModule(String name, String contents, String rootPath, boolean checkingForNonInterference, ErrorHandler errors) {
        String filePath = rootPath + "/" + (checkingForNonInterference ? (name + Constants.THREAD_MODULE_SUFFIX) : name) + ".tla";
        File file = new File(filePath);
        BufferedWriter writer = null;
        try {
            writer = new BufferedWriter(new FileWriter(file, false));
            writer.write(contents);
            writer.flush();
        } catch (IOException e) {
            errors.fatal("Could not save all generated modules", new Position(0));
            System.exit(1);
            e.printStackTrace();
        } finally {
            if(writer != null) {
                try {
                    writer.close();
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        }
    }
}
