#ifndef SEMANT_H_
#define SEMANT_H_

#include <assert.h>
#include <iostream>  
#include "cool-tree.h"
#include "stringtab.h"
#include "symtab.h"
#include "list.h"

#define TRUE 1
#define FALSE 0

class ClassTable;
typedef ClassTable *ClassTableP;

// This is a structure that may be used to contain the semantic
// information such as the inheritance graph.  You may use it or not as
// you like: it is only here to provide a container for the supplied
// methods.

class ClassTable {
private:
  int semant_errors;
  void install_basic_classes();
  ostream& error_stream;
  Classes class_lst;

  Class_ current_class_;

public:
  SymbolTable<Symbol, Entry> symbols_;

  ClassTable(Classes);
  int errors() { return semant_errors; }
  ostream& semant_error();
  ostream& semant_error(Class_ cls);
  ostream& semant_error(Symbol filename, tree_node *t);

  Class_ get_class(Symbol name);
  void set_current_class(Class_ cls);
  Class_ get_current_class();

  bool check_class_inheritance(Class_ cls);

  method_class* get_method(Class_ cls, Symbol m);
  void publish_variables(Class_ cls);
  void publish_variables(method_class* m);

  Symbol get_lc_ancestor(Class_ class1, Class_ class2);
  bool is_child_class(Class_ class1, Class_ class2);

};


#endif

