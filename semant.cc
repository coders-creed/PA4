

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <set>

#include "semant.h"
#include "utilities.h"

extern int semant_debug;
extern char *curr_filename;

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////
static Symbol 
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val,
    True,
    False;;
//
// Initializing the predefined symbols.
//
static void initialize_constants(void)
{
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy        = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    //   _no_class is a symbol that can't be the name of any 
    //   user-defined class.
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
    True        = idtable.add_string("true");
    False       = idtable.add_string("false");
}


bool ClassTable::check_class_inheritance(Class_ c) {
    int n = class_lst->len();

    int i = 0;

    Class_ parent = get_class(c->get_parent());
     
    if (parent == NULL)
    {
        semant_error(c) << "undefined parent" << std::endl; 
        return true;
    }

    while (parent->get_name() != Object)
    {
        if (parent->get_name() == Str 
                || parent->get_name() == Bool 
                || parent->get_name() == Int
                || parent->get_name() == SELF_TYPE)
            semant_error(c) << "not allowed to derive from basic classes" << std::endl;

        i++;
        
        if (i > n) 
            return true;
        
        parent = get_class(parent->get_parent());
        
        if (parent == NULL)
        {
            semant_error(c) << "undefined parent" << std::endl;   
            return true;
        }
    }
}

// initialize the class table
// add symbols for all base classes
// then add symbols for user defined classes
ClassTable::ClassTable(Classes classes) : semant_errors(0) , error_stream(cerr) 
{

    install_basic_classes();

    class_lst = append_Classes(class_lst, classes);
    std::set<Symbol> class_symbols;

    Symbol base_classes[] = {Object, Int, Bool, Str, IO, SELF_TYPE};

    for (int i = 0; i < 6; ++i)
    {
        class_symbols.insert(base_classes[i]);
    }

    // check if symbol already exists
    for (int i = classes->first(); classes->more(i); i = classes->next(i))
    {
        Class_ nth_class = classes->nth(i);

        if (class_symbols.find(nth_class->get_name()) != class_symbols.end())
        {
            semant_error(nth_class) << nth_class->get_name() << " Class has already been defined" << std::endl;
            return;
        }

        class_symbols.insert(nth_class->get_name());
        
        // find cycles in the class hierarchy
        if (check_class_inheritance(nth_class))
        {
            semant_error(nth_class) << "cyclic dependency detected" << std::endl;
            return;
        }
    }

    // check if the main class is defined
    if (get_class(Main) == NULL)
    {
        semant_error() << "Main class not defined." << std::endl;
        return;
    }
}

// get the class object from the class symbol
Class_ ClassTable::get_class(Symbol sym)
{
    if (sym == SELF_TYPE || sym == self)
        sym = symbols_.lookup(self);

    for (int i = class_lst->first(); class_lst->more(i); i = class_lst->next(i))
    {
        Class_ nth_class = class_lst->nth(i);
        // math class symbol
        if (nth_class->get_name() == sym){
            return nth_class;
        }
    }

    return NULL;
}



void ClassTable::install_basic_classes() {
    Symbol filename = stringtable.add_string("<basic class>");
    
    // initialize the class list
    class_lst = nil_Classes();

    Class_ Object_class =
	class_(Object, 
	       No_class,
	       append_Features(
			       append_Features(
					       single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
					       single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
			       single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
	       filename);
    class_lst = append_Classes(nil_Classes(), single_Classes(Object_class));
    // 
    // The IO class inherits from Object. Its methods are
    //        out_string(Str) : SELF_TYPE       writes a string to the output
    //        out_int(Int) : SELF_TYPE            "    an int    "  "     "
    //        in_string() : Str                 reads a string from the input
    //        in_int() : Int                      "   an int     "  "     "
    //
    Class_ IO_class = 
    class_(IO, 
           Object,
           append_Features(
                   append_Features(
                           append_Features(
                                   single_Features(method(out_string, single_Formals(formal(arg, Str)),
                                              SELF_TYPE, no_expr())),
                                   single_Features(method(out_int, single_Formals(formal(arg, Int)),
                                              SELF_TYPE, no_expr()))),
                           single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
                   single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
           filename);  

    class_lst = append_Classes(class_lst, single_Classes(IO_class));
    
    //
    // The Int class has no methods and only a single attribute, the
    // "val" for the integer. 
    //
    Class_ Int_class =
    class_(Int, 
           Object,
           single_Features(attr(val, prim_slot, no_expr())),
           filename);

    class_lst = append_Classes(class_lst, single_Classes(Int_class));
    //
    // Bool also has only the "val" slot.
    //
    Class_ Bool_class =
    class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);

    class_lst = append_Classes(class_lst, single_Classes(Bool_class));

    //
    // The class Str has a number of slots and operations:
    //       val                                  the length of the string
    //       str_field                            the string itself
    //       length() : Int                       returns length of the string
    //       concat(arg: Str) : Str               performs string concatenation
    //       substr(arg: Int, arg2: Int): Str     substring selection
    //       
    Class_ Str_class =
    class_(Str, 
           Object,
           append_Features(
                   append_Features(
                           append_Features(
                                   append_Features(
                                           single_Features(attr(val, Int, no_expr())),
                                           single_Features(attr(str_field, prim_slot, no_expr()))),
                                   single_Features(method(length, nil_Formals(), Int, no_expr()))),
                           single_Features(method(concat, 
                                      single_Formals(formal(arg, Str)),
                                      Str, 
                                      no_expr()))),
                   single_Features(method(substr, 
                              append_Formals(single_Formals(formal(arg, Int)), 
                                     single_Formals(formal(arg2, Int))),
                              Str, 
                              no_expr()))),
           filename);
    class_lst = append_Classes(class_lst, single_Classes(Str_class));

}

////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()                
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)  
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

// record a semantic error
ostream& ClassTable::semant_error(Class_ c)
{                                                             
    return semant_error(c->get_filename(),c);
}    

// record a semantic error
ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
{
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

// record a semantic error
ostream& ClassTable::semant_error()                  
{                                                 
    semant_errors++;                            
    return error_stream;
} 

/*   This is the entry point to the semantic checker.
 */

// overall program
void program_class::semant()
{
    initialize_constants();

    ClassTable *classtable = new ClassTable(classes);
    if (classtable->errors()) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }  
    
    classtable->symbols_.enterscope();

    classtable->symbols_.addid(True, Bool);
    classtable->symbols_.addid(False, Bool);

    for (int i = classes->first(); classes->more(i); i = classes->next(i))
    {
        Class_ c = classes->nth(i);
        Symbol name = c->get_name();
        classtable->symbols_.addid(name, name);
        c->semant(classtable);
    }

    classtable->symbols_.exitscope();

    if (classtable->errors()) {
    cerr << "Compilation halted due to static semantic errors." << endl;
    exit(1);
    } 
}

void ClassTable::set_current_class(Class_ c) 
{ 
    current_class_ = c;
}
Class_ ClassTable::get_current_class() 
{ 
    return current_class_; 
}

/* define semantic checks for each construct/production
* eg: loop, if, switch case, class definition
*/

// base object class
Symbol object_class::semant(ClassTableP classtable)
{
    if (name == self) // handle SELF_TYPE
    {
        set_type(SELF_TYPE);
        return SELF_TYPE;
    }
    
    Symbol type = classtable->symbols_.lookup(name);
                              
    if (type == NULL) 
    {
        classtable->semant_error(classtable->get_current_class()) 
            << "identifier not declared: " << name << std::endl;
        set_type(Object);
        return Object;
    }

    set_type(type);
    return type;
}

Symbol no_expr_class::semant(ClassTableP classtable)
{
    set_type(No_type);
    return No_type;
}

Symbol isvoid_class::semant(ClassTableP classtable)
{
    e1->semant(classtable);
    set_type(Bool);
    return Bool;
}

Symbol string_const_class::semant(ClassTableP classtable)
{
    set_type(Str);
    return Str;
}

Symbol new__class::semant(ClassTableP classtable)
{
    if (classtable->get_class(type_name) == NULL)
    { 
        classtable->semant_error(classtable->get_current_class()) 
            << "'new' used with undefined class " << type_name << "." << std::endl; 
        set_type(Object);
        return Object;
    }
        
    set_type(type_name);
    return type_name;
}

Symbol bool_const_class::semant(ClassTableP classtable)
{
    set_type(Bool);
    return Bool;
}

Symbol int_const_class::semant(ClassTableP classtable)
{
    set_type(Int);
    return Int;
}

Symbol comp_class::semant(ClassTableP classtable)
{
    Symbol type = e1->semant(classtable);
    if (type != Bool)
    {
        classtable->semant_error(classtable->get_current_class()) 
            << "Not requires Boolean" << std::endl; 
        set_type(Object);
        return Object;
    }

    set_type(Bool);
    return Bool;
}

Symbol leq_class::semant(ClassTableP classtable)
{
    Symbol type1 = e1->semant(classtable);
    Symbol type2 = e2->semant(classtable);

    if (type1 != Int || type2 != Int)
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Less-than-equal comparison only valid with Integers" << std::endl;
        set_type(Object);
        return Object; 
    }

    set_type(Bool);
    return Bool; 
}

Symbol eq_class::semant(ClassTableP classtable)
{
    Symbol type1 = e1->semant(classtable);
    Symbol type2 = e2->semant(classtable);

    if ((type1 == Int && type2 != Int) || 
            (type1 == Bool && type2 != Bool) ||
            (type1 == Str && type2 != Str))
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "compare only supports standard types" << std::endl;
        set_type(Object);
        return Object;
    }

    set_type(Bool);
    return Bool;
}

Symbol lt_class::semant(ClassTableP classtable)
{
    Symbol type1 = e1->semant(classtable);
    Symbol type2 = e2->semant(classtable);

    if (type1 != Int || type2 != Int)
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Less-than comparison only valid with Integers" << std::endl;
        set_type(Object);
        return Object; 
    }

    set_type(Bool);
    return Bool;
}

Symbol neg_class::semant(ClassTableP classtable)
{
    Symbol type = e1->semant(classtable);

    if (type != Int) 
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Neg used with non Integer variable" << std::endl;
        set_type(Object);
        return Object;
    }

    set_type(Int);
    return Int;
}

Symbol divide_class::semant(ClassTableP classtable)
{
    Symbol type1 = e1->semant(classtable);
    Symbol type2 = e2->semant(classtable);
    
    if (type1 != Int || type2 != Int)
    {                 
        classtable->semant_error(classtable->get_current_class()) << 
            "Divide used with non Integer variable" << std::endl;
        set_type(Object);
        return Object;
    }

    set_type(Int);
    return Int;
}

Symbol mul_class::semant(ClassTableP classtable)
{ 
    Symbol type1 = e1->semant(classtable);
    Symbol type2 = e2->semant(classtable);
    
    if (type1 != Int || type2 != Int)
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Multiply used with non Integer variable" << std::endl;
        set_type(Object);
        return Object;
    }

    set_type(Int);
    return Int;
}

Symbol sub_class::semant(ClassTableP classtable)
{ 
    Symbol type1 = e1->semant(classtable);
    Symbol type2 = e2->semant(classtable);
    
    if (type1 != Int || type2 != Int)
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Substract used with non Integer variable" << std::endl;
        set_type(Object);
        return Object;
    }

    set_type(Int);
    return Int;
}

Symbol plus_class::semant(ClassTableP classtable)
{
    Symbol type1 = e1->semant(classtable);
    Symbol type2 = e2->semant(classtable);
    
    if (type1 != Int || type2 != Int)
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Addition used with non Integer variable" << std::endl;
        set_type(Object);
        return Object;
    }

    set_type(Int);
}

Symbol let_class::semant(ClassTableP classtable)
{
    if (identifier == self)
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Can not use self as let variable" << std::endl;
        set_type(Object);
        return Object;    
    }

    Symbol type = init->semant(classtable);
    
    if (type != No_type && type != type_decl)
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Wrong type in let initialization" << std::endl;
        set_type(Object);
        return Object; 
    } 
    
    classtable->symbols_.enterscope();
    classtable->symbols_.addid(identifier, type_decl);

    Symbol type2 = body->semant(classtable);

    classtable->symbols_.exitscope();

    set_type(type2);
    return type2;
}

Symbol block_class::semant(ClassTableP classtable)
{
    Symbol type;
    for (int i = body->first(); body->more(i); i = body->next(i))
    {
        type = body->nth(i)->semant(classtable);
    }

    set_type(type);
    return type;
}

Symbol typcase_class::semant(ClassTableP classtable)
{
    Symbol type1 = expr->semant(classtable);
    Symbol type2;

    SymbolTable<Symbol, Entry> distinct_set;
    distinct_set.enterscope();

    Symbol lub = NULL;

    for (int i = cases->first(); cases->more(i); i = cases->next(i))
    {
        Symbol type_decl = cases->nth(i)->get_type();

        type2 = cases->nth(i)->semant(classtable);
        
        if (distinct_set.lookup(type_decl) != NULL)
        {
            classtable->semant_error(classtable->get_current_class()) << 
                "Branches in Case statement must be of different types" << std::endl; 
            set_type(Object);
            return Object;
        }

        distinct_set.addid(type_decl, type_decl);
        
        if (lub == NULL)
            lub = type2;

        lub = classtable->get_lc_ancestor(classtable->get_class(lub), classtable->get_class(type2));
    }

    set_type(lub);
    return lub;
}

Symbol loop_class::semant(ClassTableP classtable)
{
    Symbol type = pred->semant(classtable);

    body->semant(classtable);

    if (type != Bool)
    {
       classtable->semant_error(classtable->get_current_class()) << 
            "Loop predicate must be boolean, " << type << " given." << std::endl; 
       set_type(Object);
       return Object; 
    }

    set_type(Object);
    return Object;
}

Symbol cond_class::semant(ClassTableP classtable)
{
    Symbol type1 = pred->semant(classtable);

    if (type1 != Bool)
    { 
        classtable->semant_error(classtable->get_current_class()) << 
            "Loop predicate must be boolean, " << type << " given." << std::endl; 
        set_type(Object);
        return Object; 
    }

    Symbol type2 = then_exp->semant(classtable);
    Symbol type3 = else_exp->semant(classtable);

    Symbol type4 = classtable->get_lc_ancestor(classtable->get_class(type2), classtable->get_class(type3));

    set_type(type4);
    return type4;
}

Symbol dispatch_class::semant(ClassTableP classtable)
{
    Symbol c_type = expr->semant(classtable);

    Class_ c;

    if (c_type == No_type || c_type == SELF_TYPE) 
        c = classtable->get_current_class();
    else
        c = classtable->get_class(c_type);

    if (c == NULL)
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Tried to dispatch method on non-class" << std::endl;
        set_type(Object);
        return Object;
    }
    
    method_class *m = classtable->get_method(c, name);
    
    if (m == NULL)
    { 
        classtable->semant_error(classtable->get_current_class()) << 
            "Class " << c_type << " doesnt have method " << name << std::endl;
        set_type(Object);
        return Object;
    }

    if (actual->len() != m->get_formals()->len())
    {
        classtable->semant_error(classtable->get_current_class()) << 
            name << " expects " << m->get_formals()->len() << " parameters " << 
            actual->len() << " given" << std::endl;
        set_type(Object);
        return Object;
    }

    Formals formals = m->get_formals();
    int j = formals->first();

    for (int i = actual->first(); 
            actual->more(i); i = actual->next(i), j = formals->next(j))
    {
        Symbol type = actual->nth(i)->semant(classtable);
       
        if (!classtable->is_child_class(classtable->get_class(type), 
                    classtable->get_class(formals->nth(j)->get_type())))
        {
            classtable->semant_error(classtable->get_current_class()) << 
                name << " parameter " << i << " expected " << formals->nth(j)->get_type()
                <<  " given " << type << std::endl; 
            set_type(Object);
            return Object; 
        }
    }

    Symbol return_type = m->get_return_type();

    if (return_type == SELF_TYPE)
    {
        return_type = c_type;
    }

    set_type(return_type);
    return return_type; 
}

Symbol static_dispatch_class::semant(ClassTableP classtable)
{    
    Symbol c_type = expr->semant(classtable);

    Class_ c;

    if (c_type == No_type || c_type == SELF_TYPE) 
        c = classtable->get_current_class();
    else
        c = classtable->get_class(c_type);

    if (c == NULL)
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Tried to dispatch method on non-class" << std::endl;
        set_type(Object);
        return Object;
    }

    Class_ p = classtable->get_class(c->get_parent());

    if (!classtable->is_child_class(c, p))
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Tried static dispatch to non-parent class" << std::endl;
        set_type(Object);
        return Object;
    }
    
    method_class *m = classtable->get_method(p, name);
    
    if (m == NULL)
    { 
        classtable->semant_error(classtable->get_current_class()) << 
            "Class " << c_type << " doesnt have method " << name << std::endl;
        set_type(Object);
        return Object;
    }

    if (actual->len() != m->get_formals()->len())
    {
        classtable->semant_error(classtable->get_current_class()) << 
            name << " expects " << m->get_formals()->len() << " parameters " << 
            actual->len() << " given" << std::endl;
        set_type(Object);
        return Object;
    }

    Formals formals = m->get_formals();
    int j = formals->first();

    for (int i = actual->first(); 
            actual->more(i); i = actual->next(i), j = formals->next(j))
    {
        Symbol type = actual->nth(i)->semant(classtable);
        
        if (!classtable->is_child_class(classtable->get_class(type), 
                    classtable->get_class(formals->nth(j)->get_type())))
        {
            classtable->semant_error(classtable->get_current_class()) << 
                name << " parameter " << i << " expected " << formals->nth(j)->get_type()
                <<  " given " << type << std::endl; 
            set_type(Object);
            return Object; 
        }
    }

    Symbol return_type = m->get_return_type();

    if (return_type == SELF_TYPE)
    {
        return_type = c_type;
    }

    set_type(return_type);
    return return_type; 
}

Symbol branch_class::semant(ClassTableP classtable)
{
    classtable->symbols_.enterscope();
    classtable->symbols_.addid(name, type_decl);

    Symbol type = expr->semant(classtable);

    classtable->symbols_.exitscope();

    return type;
}

void formal_class::publish(ClassTableP classtable)
{
    if (name == self)
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Using keyword as parameter name: " << name 
            << std::endl;
        return;          
    }
    classtable->symbols_.addid(name, type_decl);
}

void attr_class::semant(ClassTableP classtable)
{
    if (name == self)
    { 
        classtable->semant_error(classtable->get_current_class()) << 
            "Using keyword as attribute name: " << name 
            << std::endl;
        return; 
    }

    Symbol type = init->semant(classtable);
    
    if (type == No_type)
    {
        return;
    }

    if (!classtable->is_child_class(classtable->get_class(type), classtable->get_class(type_decl)))
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Wrong type in attribute initialization: " << name 
            << " expected " << type_decl << " was " << type << std::endl;
        return; 
    }
}

void attr_class::publish(ClassTableP classtable)
{
    if (classtable->symbols_.lookup(name) != NULL)
    {    
        classtable->semant_error(classtable->get_current_class()) << 
            "Attribute " << name << " already defined" 
            << std::endl;
        return;    
    }

    classtable->symbols_.addid(name, type_decl);
}

Symbol assign_class::semant(ClassTableP classtable)
{
    Symbol type = classtable->symbols_.lookup(name);
                              
    if (type == NULL) 
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Identifier not declared: " << name << std::endl;
        set_type(Object);
        return Object;
    } 

    Symbol type2 = expr->semant(classtable);

    if (type != type2)
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Wrong type in assign statement" << std::endl;
        set_type(Object);
        return Object; 
    }

    set_type(type);
    return type;
}

void method_class::semant(ClassTableP classtable)
{
    classtable->symbols_.enterscope();
    publish(classtable);

    Symbol type = expr->semant(classtable);
    
    method_class *parent_method = classtable->get_method
        (classtable->get_class(classtable->get_current_class()->get_parent()), name); 

    Formals parent_formals = (parent_method != NULL) ? parent_method->get_formals() : NULL;
    
    if (return_type == SELF_TYPE && type != SELF_TYPE)
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Wrong return type in method " << name << std::endl;
        goto exit; 
    }

    if (type == SELF_TYPE)
        type = classtable->symbols_.lookup(self);

    if (classtable->get_class(return_type) == NULL)
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Undefined return type " << return_type << " in method " << name << "." << std::endl;
        goto exit;
    }

    if (!classtable->is_child_class(classtable->get_class(type), classtable->get_class(return_type)))
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Wrong return type in method " << name << " expected " << return_type 
            << " found " << type <<  std::endl;
        goto exit;
    }

    if (parent_method && parent_method->get_formals()->len() != formals->len())
    {    
        classtable->semant_error(classtable->get_current_class()) << 
            "Wrong number of parameters in method override " << name <<  std::endl;
        goto exit; 
    }
    
    for (int i = formals->first(); formals->more(i); i = formals->next(i))
    {          
        if (formals->nth(i)->get_type() == SELF_TYPE)
        { 
            classtable->semant_error(classtable->get_current_class()) << 
                "Formal parameter " << name << " cannot have type SELF_TYPE"
                << std::endl;
            goto exit;    
        }

        if (parent_method && parent_formals->nth(i)->get_type() != formals->nth(i)->get_type())
        {
            classtable->semant_error(classtable->get_current_class()) << 
                "Wrong parameter type in method override."
                << std::endl;
            goto exit; 
        }
    }          

exit:
    classtable->symbols_.exitscope();
}

void method_class::publish(ClassTableP classtable)
{
    SymbolTable<Symbol, Entry> params;
    params.enterscope();

    for (int i = formals->first(); formals->more(i); i = formals->next(i))
    {
        Formal_class *formal = formals->nth(i);

        if (params.lookup(formal->get_name()) != NULL)
        {
            classtable->semant_error(classtable->get_current_class()) << 
                "Duplicated parameter name " << formal->get_name() 
                << " in method " << name << std::endl;
            return; 
        }

        params.addid(formal->get_name(), formal->get_name());

        formal->publish(classtable);
    }

    params.exitscope();
}

void class__class::semant(ClassTableP classtable)
{
    if (parent == SELF_TYPE)
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Not a valid parent " << parent <<  std::endl; 
        return;
    }

    if (classtable->get_class(parent) == NULL)
    {
        classtable->semant_error(classtable->get_current_class()) << 
            "Not a valid parent " << parent <<  std::endl; 
        return;
    }

    classtable->symbols_.enterscope();
    classtable->set_current_class(this);
    classtable->symbols_.addid(self, classtable->get_current_class()->get_name());
    classtable->publish_variables(this);
    for (int i = features->first(); features->more(i); i = features->next(i))
    {
        features->nth(i)->semant(classtable);
    }
    classtable->symbols_.exitscope();
}


//////////////////////////////////////////////
// member functions
//////////////////////////////////////////////
Symbol ClassTable::get_lc_ancestor(Class_ c1, Class_ c2)
{
    if (c1->get_name() == c2->get_name())
        return c1->get_name();
    
    SymbolTable<Symbol, Entry> parents;
    parents.enterscope();
    parents.addid(c1->get_name(), c1->get_name());

    Class_ p1 = get_class(c1->get_parent());
    while (p1 != NULL)
    {
        parents.addid(p1->get_name(), p1->get_name());
        p1 = get_class(p1->get_parent());
    }

    Class_ p2 = c2;
    while (p2 != NULL)
    {
        if (parents.lookup(p2->get_name()) != NULL)
            return p2->get_name();

        p2 = get_class(p2->get_parent());
    }

    return Object;
}

method_class* ClassTable::get_method(Class_ c, Symbol m)
{
    for (int i = c->get_features()->first(); c->get_features()->more(i); i = c->get_features()->next(i))
    {
        method_class *method = dynamic_cast<method_class*>(c->get_features()->nth(i));
        
        if (method == NULL) 
            continue;

        if (method->get_name() == m)
        {
            return method;

        }
    }
    
    Class_ p = get_class(c->get_parent());
    return (p == NULL) ? NULL : get_method(p, m);
}

bool ClassTable::is_child_class(Class_ c1, Class_ c2)
{
    if (c1->get_name() == c2->get_name())
        return true;

    Class_ p = get_class(c1->get_parent());

    return (p == NULL) ? false : is_child_class(p, c2);
}

void ClassTable::publish_variables(Class_ c)
{
    Features features = c->get_features();
    for (int i = features->first(); features->more(i); i = features->next(i))
    {
        attr_class *attr = dynamic_cast<attr_class*>(features->nth(i));
        
        if (attr == NULL)
            continue;

        attr->publish(this);
    }

    Class_ p = get_class(c->get_parent());
    if (p != NULL) 
    {
        publish_variables(p);
    }
}

void ClassTable::publish_variables(method_class* m)
{
    
}
//////////////////////////////////////////////















