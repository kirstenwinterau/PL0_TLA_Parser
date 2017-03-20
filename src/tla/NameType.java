package tla;

import syms.Type;

/*
 * Represents a variable by its name and type, used to pass around TLA+ variables
 * without the unnecessary information of symtab entries or tree nodes
 */
public class NameType {
    public String name;
    public Type type;
    
    public NameType(String name, Type type) {
        this.name = name;
        this.type = type;
    }
    
    @Override
    public boolean equals(Object o) {
        if (!(o instanceof NameType)) return false;
        NameType n = (NameType) o;
        // Variables are considered equal if their names are equal, since only one variable of
        // a given name is allowed in both the TLA+ specification and PL/0 program
        return (n.name.equals(this.name));
    }
    
    @Override
    public int hashCode() {
        int result = name.hashCode();
        return result;
    }
}
