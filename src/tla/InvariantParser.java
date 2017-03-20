package tla;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import source.ErrorHandler;
import source.Position;
import syms.Constants;

/**
 * Parses a TLA+ invariant, expected to be of a form where constraints on the 
 * program counter imply some logic. 
 */
public class InvariantParser {
    // Raw invariant as it was input by the user
    private String rawInvariant;
    // Maps pc values (with optional T or F postfix) to any relevant sections of the invariant
    private Map<String, String> sectionsByPc;
    
    public InvariantParser(String invariant) {
        this.rawInvariant = invariant;
        sectionsByPc = new HashMap<String, String>();
        parseInvariant();
    }
    
    public Map<String, String> getSections() {
        return sectionsByPc;
    }
    
    public String getRawInvariant() {
        return rawInvariant;
    }
    
    private void parseInvariant() {
        boolean removeBracket = false;
        boolean removeNextBracket = false;
        Matcher whitespaceMatcher = Pattern.compile("\\s").matcher(rawInvariant);
        String result = whitespaceMatcher.replaceAll(" ");
        result = result.trim();
        
        // Add whitespace as pattern matching requires non alphanumeric characters each side of 'pc'
        result = " " + result;
        
        // Split on string 'pc' where it follows a non alphanumeric character
        String[] rawSections = result.split("[^a-z[^A-Z[^0-9]]]pc");
        List<String> sections = new ArrayList<String>();
        sections.add(rawSections[0]);
        
        // Loop over the split string, if the first character is alphanumeric then we have
        // split on a variable name that starts with pc and need to undo this split
        for(int i=1; i<rawSections.length; i++) {
            String s = rawSections[i];
            if(Character.isDigit(s.charAt(0)) || Character.isLetter(s.charAt(0))) {
                sections.set(sections.size() - 1, sections.get(sections.size() -1) + s);
            } else {
                sections.add(s);
            }
        }
        
        // Loop over the invariant sections (each constrained by pc)
        for(int i=0; i < sections.size(); i++) {
            removeNextBracket = false;
            String s = sections.get(i).trim();
            
            // Remove excess escape characters (from conjunctions) at end of segment
            while(s.endsWith("/") || s.endsWith("\\")) {
                s = s.substring(0, s.length() - 1);
                s = s.trim();
            }
            // Remove excess brackets at end of segment
            if(s.endsWith("(")) {
                removeNextBracket = true;
                s = s.substring(0, s.length() - 1);
                s = s.trim();
            }
            

            s = s.trim();
            if(removeBracket && s.endsWith(")")) {
                s = s.substring(0, s.length() -1 );
                s = s.trim();
            }
            
            // Matching a single pc value
            if (s.startsWith("=")) {
                s = s.substring(1);
                s = s.trim();
                // Find the next integer representing the pc value
                Matcher m = Pattern.compile(Constants.PC_VALUE_REGEX).matcher(s);
                String pc = "error";
                if(m.find()) {
                    s = s.substring(m.group(0).length());
                    pc = m.group(0);
                }
                pc = pc.trim();
                s = s.trim();
                // Find the start of the logic associated with the pc value
                m = Pattern.compile("=>").matcher(s);
                Matcher p = Pattern.compile("/").matcher(s);
                if((m.find() && m.start() == 0) || (p.find() && p.start() == 0)) {
                    s = s.substring(2);
                    s = removeExtraBracket(s);
                    if (sectionsByPc.containsKey(pc)) {
                        result = sectionsByPc.get(pc);
                        result += " /\\ ";
                        result += s;
                        sectionsByPc.put(pc, result);
                    } else {
                        sectionsByPc.put(pc, s);
                    }
                }
            // Matching a list/range of pc values
            } else if (s.startsWith("\\in")) {
                s = s.substring(3);
                s = s.trim();
                s =  "\\union " + s;
                List<String> pcs = new ArrayList<String>();
                while(s.startsWith("\\union")) {
                    s = s.substring(6);
                    s = s.trim();
                    // pc values are specified in a set
                    if(s.startsWith("{")) {
                        s = s.substring(1);
                        s = s.trim();
                        int end = s.indexOf("}");
                        // Find all digits separated by non-numeric chars or whitespace
                        Matcher d = Pattern.compile(Constants.PC_VALUE_REGEX).matcher(s.substring(0, end));
                        while(d.find()) { 
                            pcs.add(d.group(0).trim());
                        }
                        s = s.substring(end + 1);
                        s = s.trim();
                    // pc values specified as a range
                    } else {
                        Matcher d = Pattern.compile("\\d+").matcher(s);
                        int start = 0;
                        int end = 0;
                        // Find the lower bound
                        if(d.find()) {
                            start = Integer.parseInt(d.group(0));
                        }
                        s = s.substring(d.group(0).length());
                        s.trim();
                        if(s.startsWith("..")) {
                            s = s.substring(2);
                            s.trim();
                        }
                        // Find the upper bound
                        d = Pattern.compile("\\d+").matcher(s);
                        if(d.find()) {
                            end = Integer.parseInt(d.group(0));
                            s = s.substring(d.group(0).length());
                        } else {
                            end = start;
                        }
                        for(int j = start; j <= end; j++) {
                            pcs.add(Integer.toString(j));
                        }
                    }
                    s = s.trim();
                }
                if(s.startsWith("=>") || s.startsWith("/\\")) {
                    s = s.substring(2);
                }
                s = s.trim();
                s = removeExtraBracket(s);
                
                // Map new predicates to relevant pc value(s)
                for(String pc: pcs) {
                    if (sectionsByPc.containsKey(pc)) {
                        result = "(" + sectionsByPc.get(pc) + ")";
                        result += " /\\ ";
                        result += "(" + s + ")";
                        sectionsByPc.put(pc, result);
                    } else {
                        sectionsByPc.put(pc, s);
                    }
                }
                
            }
            removeBracket = removeNextBracket;
        }
        /*Matcher matcher = Pattern.compile("pc").matcher(result);
        while (matcher.find()) {
            //(Debug) System.out.println("Found: " + matcher.group(0));
        }*/
    }
    
    public void printInvariantSections() {
        for(String pc: sectionsByPc.keySet()) {
            System.out.println(pc + sectionsByPc.get(pc));
        }
    }
    
    // Get the invariant specific to a given program counter value
    public String getInvariantForPc(String pc) {
        String result = sectionsByPc.get(pc);
        if(result == null) {
            result = "TRUE";
        }
        return result;
    }
    
    /**
     * Check we have a balanced number of brackets, if we have one more right bracket
     * than left bracket it is because the first left bracket was chopped out by the 
     * regex for splitting up the invariant (which potentially matches "(pc")
     * @param s The string to check for an extra bracket
     * @retruns The string with the extra bracket removed, if present
     */
    private String removeExtraBracket(String s) {	
        int numLeftBrackets = 0;
        int numRightBrackets = 0;
        for(char c : s.toCharArray()) {
            if(c == '(') {
                numLeftBrackets++;
            } else if (c == ')') {
                numRightBrackets++;
            }
        }
        if(numLeftBrackets < numRightBrackets && s.endsWith(")")) {
            s = s.substring(0, s.length() - 1);
        }
        return s;
    }
    
    // Replaces all references to local variables with  
    public static String getInvariantForOtherThread(List<String> localVars, String rawInvariant) {
        Pattern variable = Pattern.compile(Constants.VARIABLE_NAME_REGEX);
        Matcher m = variable.matcher(rawInvariant);
        String invariant = rawInvariant;
        int charsAdded = 0;
        while(m.find()) {
            if(m.group().equals("in") && m.start() > 0) {
                if(rawInvariant.charAt(m.start() - 1) == '\\') {
                    continue;
                }
            }
            // Access to instance variable, local variable name will be first component
            String[] values = m.group().split(".");
            String value = values.length > 0 ? values[0] : m.group();
            if(localVars.contains(value)) {
                int start = m.start() + charsAdded;
                int size = value.length();
                invariant = invariant.substring(0, start) + value + syms.Constants.THREAD_SUFFIX + invariant.substring(start + size);
                charsAdded++;
            }
        }
        System.out.println(invariant);
        return invariant;
    }
    
    /**
     * Finds each of the invariants (ABS, INV etc) and status transitions in the given file if they 
     * are present, otherwise they will be set to a default. Returns them in a map indexed by their name.
     * 
     * @param stream The file to parse the invariants from (the root module of the TLA spec)
     * @return a map of names (e.g. ABS, D, IN_OUT) to the corresponding TLA+ input by the user
     */
    public static Map<String, String> parseInvariantsFromFile(FileReader stream, ErrorHandler errors) {
        List<String> requiredInvariants = new ArrayList<String>(Arrays.asList(Constants.REQUIRED_INVARIANTS));
        
        List<String> transitions = Arrays.asList(Constants.STATUS_TRANSITIONS);
        requiredInvariants.addAll(transitions);
        
        Map<String, String> invariants = new HashMap<String, String>();
        
        BufferedReader file = new BufferedReader(stream);
        String line;
        // Used to parse extra invariants from the top of the file, these are assumed to belong to ABS
        boolean firstInvFound = false;
        String extras = "";
        try {
            line = file.readLine();
            String currentName = "";
            boolean alreadyAdded;
            while(line != null) {
                String lineWithWhitespace = line;
                line = line.trim();
                alreadyAdded = false;
                // Identify the beginning of an invariant we care about
                for(String inv: requiredInvariants) {
                    if(line.startsWith(inv)) {
                        // Get the right hand side of the definition if it exists
                        String[] components = line.split("==", 2);
                        if(components.length != 2 || !components[0].trim().equals(inv) || components[1].trim().isEmpty()) {
                            continue;
                        }
                        currentName = inv;
                        firstInvFound = true;
                        invariants.put(currentName, components[1]);
                        alreadyAdded = true;
                        continue;
                    }
                }
                // Want to keep the list of constants & extends modules so we can replicate it in all the generated modules
                if(line.startsWith("CONSTANT")) {
                    String constants = line.substring(8);
                    invariants.put("CONSTANT",constants);
                }
                if(line.startsWith("EXTENDS")) {
                    String extendsModules = line.substring(7);
                    invariants.put("EXTENDS", extendsModules);
                }
                // Keep the extra invariants before the first regular invariant is found, these extras
                // are assumed to be associated with ABS. This is also a special case where we want to
                // keep the original indentation for readability, we are not extracting parts out on a 
                // per-line basis
                if(!firstInvFound && !line.startsWith("EXTENDS") && !line.startsWith("VARIABLE")
                        && !line.startsWith("CONSTANT") && !line.isEmpty() && !line.startsWith("--") && !line.startsWith("\\*")) {
                    extras = extras + lineWithWhitespace + System.lineSeparator();
                }
                // We have a blank line or the end of the module, either way are finished
                // the current invariant
                if(line.trim().isEmpty() || line.trim().startsWith("==")) {
                    currentName = "";
                }
                // We are still parsing the same invariant as before, add the next line of TLA.
                // ABS is a special case where we keep the original indenting for readability,
                // as we won't be manipulating ABS further
                if(!currentName.isEmpty() && !alreadyAdded) {
                    invariants.put(currentName, invariants.get(currentName) == null ? 
                            line : (invariants.get(currentName) + System.lineSeparator() + 
                                    (currentName.equals("ABS") ? lineWithWhitespace : line)));
                
                }
                line = file.readLine();
            }
        } catch (IOException e) {
            errors.fatal("Reading TLA invariants from root module was unsucessful", new Position(0));
            errors.flush();
            System.exit(1);
            e.printStackTrace();
        } finally {
            try {
                file.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
        
        // Check we have all the invariants we need, if not we add 
        // the default value 
        for(String inv: requiredInvariants) {
            if(!invariants.containsKey(inv)) {
                // Default for status transitions is false
                if(Arrays.asList(Constants.STATUS_TRANSITIONS).contains(inv)) {
                    invariants.put(inv, "FALSE");
                 // Default for invariants like ABS is true
                } else {
                    invariants.put(inv, "TRUE");
                }
            }
        }
        
        // Add extras from top of file to ABS
        // Additionally, since we don't parse abs, so we want to keep ABS== segment on front
        invariants.put("ABS", extras + "ABS ==" + invariants.get("ABS"));
        return invariants;
    }
}
