from dataclasses import is_dataclass, dataclass
from typing import List, Optional

@dataclass(frozen=True)
class Type:
    basic_type: type
@dataclass(frozen=True)
class IntType(Type):
    def __init__(self):
        super().__init__(int)
    def __str__(self):
        return "int"

@dataclass(frozen=True)
class FloatType(Type):
    def __init__(self):
        super().__init__(float)
    def __str__(self):
        return "float"

@dataclass(frozen=True)
class StrType(Type):
    def __init__(self):
        super().__init__(str)
    def __str__(self):
        return "str"

@dataclass(frozen=True)
class ComplexType(Type):
    def __init__(self):
        super().__init__(complex)
    def __str__(self):
        return "complex"

@dataclass(frozen=True)
class BoolType(Type):
    def __init__(self):
        super().__init__(bool)
    def __str__(self):
        return "bool"
#*******************************************************************************
class ProgramModel:
    def __init__(self):
        self.args = []           # The inputs which is list of InputArgument_variables
        self.assumptions = []    # The assumptions which is list of LocalVariable_variables
        self.variables = dict()  # A dictionary which contains all InputArgument(s) and LocalVariable(s) with their types
        self.return_expression = None
        self.return_type = None
        self.description = None
        #When the statements list is never empty, it contains at least a representation of the last hole
        #self.statements = ["    ***   [" + str(len(self.args) + len(self.assumptions))+ "]  ***"]
        self.statements = ["    ***   [0]  ***"]
        self.switch_mode = False; self.switch_pointer = 0 # both serve for switch_handler
    @property
    def args_names_list(self):
        return [names.name for names in self.args if names]
    @property
    def args_types_list(self):
        return [full_types.full_type for full_types in self.args if full_types]
    @property
    def assumptions_names_list(self):
        return [names.name for names in self.assumptions if names]
    @property
    def assumptions_types_list(self):
        return [full_types.full_type for full_types in self.assumptions if full_types]
    def __str__(self):
        lines = []
        #show description
        if self.description:
            lines.append("#" +self.description)
        # After you have given the sigature, show me the functions_head and return    
        if self.name:
            arg_list = []
            if len(self.args) > 0:
                for arg in self.args:
                    arg_line = str(arg.name) + ": " + str(arg.full_type)
                    arg_list.append(arg_line)
            line = "def "+ str(self.name) + " ("+ ", ".join(arg_list)+ ") -> "+ str(self.return_type) + ":"
            lines.append(line)

            if self.assumptions :
                for assumption in self.assumptions:
                    lines.append("    " +str(assumption))
                    
            #show return after assumptions when they are available if not then a hole
            if self.return_expression != None:#not in (None, ""):
                lines.append("    return " + str(self.return_expression))
            else:
                lines.append(self.statements[0])
                    
            #merge all to one string
        return "\n".join(lines)

    #def update_return_field(self):
    #    """A function which concerns about increasing the number of last hole, will be called many times """
     #   anzahl = len(self.args) + len(self.assumptions)
     #   self.statements[0] = "    ***   [" + str(len(self.args) + len(self.assumptions)) +"]  ***"
    def update_return_field(self):
        """A function which updates the last hole representation safely"""
        anzahl = len(self.args) + len(self.assumptions)
        text = f"    ***   [{anzahl}]  ***"
        if not self.statements:   # falls die Liste leer ist
            self.statements.append(text)
        else:
            self.statements[0] = text

    def update_holes_index(self):
        for i,var in enumerate(self.assumptions):
          var.temporary_value =  f"** [{i + len(self.args)}] **"

class Variable:
    class LocalVariable:
        def __init__(self,type_obj:Type, return_type:Type, name:str):
            self.full_type = type_obj # for function type, full_ttype and return_type
            self.return_type = return_type
            self.name = name
            self.value = None
            self.temporary_value = None #like ** [2] ** will be filled in save_local_variables temporarily, till we have value for this variable

        def __str__(self):
            if self.value is not None:
                return f"{self.name} = {self.value}"
            else:
                return f"{self.name} = {self.temporary_value}"

    class InputArgument:
        def __init__(self, type_obj:Type, return_type:Type):
            self.full_type = type_obj # for function type, full_ttype and return_type
            self.return_type = return_type
            self.name = None

        def __str__(self):
            return f"InputArgument({self.full_type}, {self.return_type}, {self.name})"
