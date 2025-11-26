import parser
import re, builtins, ast, keyword #,types, typing, math, operator, ast
from data_model import ProgramModel, Variable, Type, IntType, FloatType, ComplexType, StrType, BoolType #, NoneType

#global variables
modus = ""
BASIC_TYPES = {"int", "complex", "bool", "float", "str"}
dummy_values = {'int': 1,'float': 0.1,'str': '" "','complex': 1 + 1j,'bool': True, 'None': ''}
class CommandFSM:
    def __init__(self, model):
        self.state = "START"
        self.prev_state = "START"
        self.transitions = {"START": ["description:"], "DESCRIPTION": ["signature:"], "SIGNATURE":["intro:"],"INTRO_MAIN": ['let:', "return:"],
                            "INTRO": ["let:", "fill:", "return:", "switch:"], "SWITCH":["fill:", "return:", "let:"],
                            "FILL": ["let:", "fill:","return:", "switch:"], "RETURN": ["fill:", "finish:", "switch:"], "FINISH": [] }
        self.prefix_to_state = { "description:": "DESCRIPTION", "signature:": "SIGNATURE", "intro_main:": 'INTRO_MAIN', "intro:": 'INTRO',
                                 "let:": "INTRO", "switch:":"SWITCH", "fill:": "FILL", "return:": "RETURN", "finish:": "FINISH" }
        self.given = { "description": False, "signature": False, "intro_main": False, "intro": False,
                       "fill": False, "return":False, "finish": False }
    def go_to_the_first_empty(self):
        def versuch():
            prev = ""
            for key, value in self.given.items():
                if key == "description" and not value:
                    return "START"
                if value:
                    prev = key
                if not value:
                    break
            return prev
        result = versuch()
        if result == "START":
            return "START"   
        else:
            result = result + ":"
            return self.prefix_to_state[result]
        
    def check_and_advance(self, command, model):
        #first check, if we can go to the first empty
        next_state = self.go_to_the_first_empty()
        if self.state != next_state:
            #ignore actual command because we must firstly fill the gaps
            self.state = next_state
            return #Stop, we will not continue with this command

        allowed_prefixes = self.transitions[self.state]
        matched_prefix = None
        
        for prefix in allowed_prefixes:
            if command.startswith(prefix):
                matched_prefix = prefix
                break
        if matched_prefix is None:
            raise ValueError(f"Invalid command '{command}' in state '{self.state}'.Allowed prefixes: {allowed_prefixes}")
        self.state = self.prefix_to_state[matched_prefix]
#::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
#Helper function(s) for the program
#::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
def replace_variables_with_dummy(s,model) -> str:
    """ replace_variables_with_dummy("a+b+c",model)->'1+1+1' kommen wenn a und b und c are of type int """
    #make a new dictionary out of model.variables which contains the variables of the model which their value != None
    only_variables_with_values = dict()
    only_variables_with_values = {item.name: item.full_type for item in model.args}
    only_variables_with_values.update({a.name: a.full_type for a in model.assumptions if a.value is not None})         
    #Sort variable names in descending order of length to prevent conflicts like 'a' occurring within 'abc'
    sorted_vars = sorted(only_variables_with_values, key=lambda x: -len(x))
    for var in sorted_vars:
        var_type = str(only_variables_with_values[var])
        dummy = dummy_values[var_type]
        #matches only isolated variables (only whitespace can occur, no letters or digits)
        pattern = rf'(?<!\w)(\s*){re.escape(var)}(\s*)(?!\w)'
        #Replace function which preserves whitespace and replaces only the variable_name
        def replacer(match):
            before = match.group(1)
            after = match.group(2)
            return f"{before}{dummy}{after}"
        s = re.sub(pattern, replacer, s)
    return s
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def existing_variable(variable, model) -> bool:
    """ This helper funtion checks if this variable is already in the assumptions list"""
    if variable in model.assumptions_names_list:
        return True
    return False
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def move_to_the_first_open_hole(model) -> None:
    """ Helper fundtion for switch_handler, which shows an important msg """
    if any(assumption.value is None for assumption in model.assumptions):
        ind = next(i for i, var in enumerate(model.assumptions) if var.value is None) +  len(model.args)
    print(f".. you will be redirected to the first open hole, which is the {ind}th hole")
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def save_assumptions(assumption:str, model) -> bool:
    """ This function will be used in fill_handler to save the value of some local variable,
        when it gives True it means a variable has been filled successfully """
    original_assum_value = assumption.strip()
    #The index will be different, according if switch is on
    if model.switch_mode == True:
        my_index = model.switch_pointer - len(model.args)
    else:
        my_index = next((i for i, sublist in enumerate(model.assumptions) if None == sublist.value), None)
    assum_name = model.assumptions_names_list[my_index]
    assum_type = extract_the_type(original_assum_value, model)
    if str(model.assumptions_types_list[my_index]) != str(assum_type):
        print ("The type does not match!")
        return False
    else:
        #save assumptions operation
        if model.switch_mode:
            model.assumptions[my_index].value = original_assum_value
        else: 
            for var in model.assumptions:
                if var.value is None:
                    var.value = original_assum_value
                    break  #Just the first assumption, which has no value. then leave
        model.variables[assum_name] = assum_type
        model.switch_mode = False
    return True
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def save_local_variables(assumption:str, model) -> bool:
    """ Helper function which is used in let_handler to save local variable, it gives back True when the local variable has been saved successfully  """
    part1_index = assumption.find("(")
    part2_index = assumption.rfind(")")
    assum_name , assum_value = assumption[part1_index+1:part2_index].split(":")
    assum_name = assum_name.strip()
    assum_value = assum_value.strip()
    if not parser.is_valid_name(assum_name):
        print("Invalid variable name!")
        return False
    if assum_name in model.args_names_list:
        print('You are not allowed to use the input names of the main function ans local variables!')
        return False
    elif assum_value not in BASIC_TYPES:
        print('Invalid type!')
        return False
    #we can't change the value of a variable, but we can delete it and then add it again (not at the same old index)
    elif existing_variable(assum_name, model):
        #delete him and his value from the list , and save it again
        indexi = next((i for i, sublist in enumerate(model.assumptions) if assum_name == sublist.name), None)
        if len(model.statements)-1 >= indexi:
            del model.statements[indexi]
        model.variables.pop(assum_name)
        del model.assumptions[indexi]
        return save_local_variables(assumption, model)
    else:
        new_local_variable= Variable.LocalVariable(assum_value, assum_value, assum_name)
        Anz_args = len(model.args)+len(model.assumptions)
        new_local_variable.temporary_value = f"***  [{ Anz_args }]  ***"
        model.update_return_field(); model.update_holes_index()
        model.assumptions.append(new_local_variable)
        model.variables[assum_name] = assum_value    
        return True
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def typ_kompatibel(actual: str, expected: str) -> bool:
    """ Helper function for überprüfe_rückgabe_typ which checks wether two types are compatible """
    if actual == "bool" and expected != "bool":
        return False
    if expected == actual:
        return True
    if expected == str and actual != str:
        return False
    if expected == "float" and actual == "int":
        return True
    if expected == "int" and actual == "float":
        return False
    if expected == "complex" and actual == 'int':
        return True
    else:
        return False
    return False
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def überprüfe_rückgabe_typ(expr: str, rueckgabe_typ: str, model) -> bool:
    """ This function checks the type for the 3 types: complex, int, float, e.g:
        überprüfe_rückgabe_typ(' 5.6+6 ', 'float', model) -> True """
    expr = replace_variables_with_dummy(expr, model)
    try:
        #use Ast, to read the code before you run it block not desired things before they happen, like strings
        tree = ast.parse(expr, mode='eval')
        #block the strings, we have another special function for them
        for node in ast.walk(tree):
            if isinstance(node, ast.Constant) and isinstance(node.value, str):
                return False
        #run the expression without access to python_builtins
        result = eval(expr, {"__builtins__": None})
        actual_type_str = type(result).__name__
        return typ_kompatibel(actual_type_str, rueckgabe_typ)
    except Exception:
        return False
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def is_boolean_expression(expr: str, model) -> bool:
    """ This function checks for boolean: is_boolean_expression('True or False', model) -> True """
    try:
        #replace the variables of your model with dummy_values
        expr = replace_variables_with_dummy(expr, model)
        #evaluate the expression
        result = eval(expr, {"__builtins__": None})
        #check if the result is bool
        return isinstance(result, bool)
    except Exception:
        return False
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def is_string(s, model) -> bool:
    try:
        context = {var: val for var, val in model.variables.items()}
        return isinstance(eval(s, {"__builtins__": None}, context), str)
    except Exception:
        return False
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def extract_the_type(expression, model) -> Type:
    """ This function transforms the python types into our own types(IntType ,BoolType,...) """
    expression = replace_variables_with_dummy(expression,model)
    if is_string(expression, model):
        return StrType()
    elif überprüfe_rückgabe_typ(expression, 'int' ,model):
        return IntType()
    elif überprüfe_rückgabe_typ(expression, 'float' ,model):
        return FloatType()
    elif überprüfe_rückgabe_typ(expression, 'complex' ,model):
        return ComplexType()
    elif is_boolean_expression(expression, model):
        return BoolType()
    else:
        return None
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * 
def check_the_type(expression, expected_type ,model) -> bool:
    """ This function checks wether the expession has the expected type, e.g:
        check_the_type('5+"s"', StrType() ,model) -> False"""
    expression = replace_variables_with_dummy(expression,model)
    if is_string(expression, model) and (expected_type == StrType() or str(expected_type) == 'str'):
        return True
    elif überprüfe_rückgabe_typ(expression, str(expected_type) ,model):
        return True  
    elif is_boolean_expression(expression, model) and (expected_type == BoolType() or str(expected_type) == 'bool'):
        return True
    else:
        return False
####END OF HELPER FUNCTIONS####   &  ####START OF MAIN_FUNCTIONS####
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def description_handler(command, model, fsm) -> bool:
    """ description_handler('description: A simple program', model, fsm) ->  #A simple program """
    try:
        res = fsm.check_and_advance(command, model)
        model.description = command[len("description:"):].strip()
        fsm.given["description"] = True
        if modus == "interaktiv":
            print("Description part is saved *_*")
    except ValueError as e:
        print(f"{str(e)}")
    return False
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def signature_handler(command, model, fsm) -> bool:
    """ signature_handler(signature: main: (int, bool) -> str, model, fsm) -> def main (arg[0]:int, args[1]:bool) -> str: """
    try:
        res = fsm.check_and_advance(command, model)
        part = command[len("signature:"):].strip()
        if ':' not in part:
            print("Signature has not the right Format!")
            fsm.state = "DESCRIPTION"
            return False        
        else:
            part = command[len("signature:"):].strip()
            name_and_types = part.split(":")
            if not parser.is_valid_name(name_and_types[0].strip()):
                print("Invalid function name!")
                fsm.state = "DESCRIPTION"
                return False
            model.name = name_and_types[0].strip()
            types_part = name_and_types[1].strip()
            args_part, return_type = parser.split_on_last_arrow(types_part.strip())
            #check signature format
            if parser.parse_type(str(types_part)):
                model.return_type = return_type.strip()
                args_part = args_part.strip()
                #fill the types in the model
                if parser.extract_direct_types(types_part, model) != True:
                    print('Signature format is not ok!')
                    return False
                s = args_part
                #i need length of '(   )', '   ()' to be zero. Do regular expression(regex) matching
                if not bool(re.fullmatch(r'\s*\(\s*\)\s*', s)):
                    for i,lst in enumerate(model.args):
                        lst.name = "agr[" + str(i) + "]" 
                model.update_return_field(); model.update_holes_index()
                print("\n", model, sep="")
                fsm.given["signature"] = True
                if modus == "interaktiv":
                    print("Signature part is saved *_*")
            else:
                print("Signature has not the right Format!")
                fsm.state = "DESCRIPTION"
                return False
    except ValueError as e:
        print(f"{str(e)}")
        return False
    return False
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def let_handler(command, model ,fsm) -> bool:
    """ let_handler('let: (x:int)', model ,fsm) -> x = [some_hole_number]"""
    if fsm.given['return'] == True:
        print('You are not allowed to intialize new variables after you have filled the reutrn hole.')
        return False
    try:
        res = fsm.check_and_advance(command, model)
        local_variable = command[len("let:"):].strip()       
        resi = save_local_variables(local_variable, model)
        if resi == True:
            fsm.state = "INTRO"; fsm.given["intro"] = True
            model.update_return_field(); model.update_holes_index()
            if modus == "interaktiv":
                print("A local variable has been saved!")
            print("\n", model, sep="")
        else:
            print("Assumption is not ok. There is something wrong!")
            fsm.state = "INTRO_MAIN"
            return False
    except ValueError as e:
        print(f"{str(e)}")
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def intro_handler(command, model, fsm) -> bool:
    """ intro_handler('intro: n b', model ,fsm) -> def main (n:int, b:bool) -> str: 
         attention: even when there is no intro, this command must always be given"""
    if fsm.given["return"] == True:
        print('After you have filled the return hole, you are not allowed to give any assumptions more')
        fsm.state = "RETURN"
        return False
    try:
        res = fsm.check_and_advance(command, model)
        part = command[len("intro:"):].strip()
        if fsm.given["intro_main"] != True:
            result= ""
            Teils = part.split()
            if len(Teils) == len(model.args):
                result = all(Teil.isalpha() for Teil in Teils)
            else:
                print('The Length of names != Length of types')
                fsm.state = "SIGNATURE"
                return False
            if result == True:
                names = part.split(" ")
                arg_names = []
                if names == [''] and len(model.args_types_list) == 0:
                    resi = True
                else:
                    for name in names:
                        if names.count(name) > 1:
                            print("You can not have repeated inputs")
                            fsm.state = "SIGNATURE"
                            return False
                    else:
                        name = name.strip()
                        if len(model.args) > 0:
                            for i,input_argument in enumerate(model.args):
                                input_argument.name = names[i] 
                                model.variables[names[i]] = next(
                                        (lst.return_type for lst in model.args if lst.name == names[i]), None)
                            resi = True
                if resi == True:
                    model.update_return_field(); model.update_holes_index()
                    print("\n", model, sep="")
                    fsm.state = "INTRO_MAIN"; fsm.given["intro_main"] = True
                    if modus == "interaktiv":
                        print("intro part is saved *_*")
                        return 
            elif fsm.given["intro_main"] == True:
                print("you have already given the inputs!")
                fsm.state = "INTRO_MAIN"
                return False
            elif result == False:
                fsm.state = "SIGNATURE"
                print("Something in your syntax is wrong!")
                return False
    except ValueError as e:
        print(f"{str(e)}")
    return False
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def switch_handler(command, model, fsm) -> bool:
    """ This function goes internally to the desired hole, if it is available but if not then it goes to the first open hole in the program 
        user gives things like:  switch: 2     """
    try:
        res = fsm.check_and_advance(command, model)
        Hole_index = command[len("switch:"):].strip()
        if not isinstance(eval(Hole_index), int):
            print('Invalid input!')
        Hole_index = int(Hole_index)
        model.switch_mode = True
        if Hole_index <= len(model.args) - 1:
            print('\n'+'This Hole is reserved for input names and not allowed to be filled twice!')
            model.switch_mode = False
            return False
        elif Hole_index == len(model.args) + len(model.assumptions):
            if fsm.given['return'] == True:
                print('\n'+'This is the return hole which is already filled.')
                move_to_the_first_open_hole(model)
                model.switch_mode = False
                return False
            elif fsm.given['return'] == False:
                print('\n'+'ok you are now in the last hole!, you can intialize new variables or fill the return')
            fsm.state = 'SWITCH'
            return False
        elif Hole_index >= len(model.args) + len(model.assumptions) + 1: # +1 becauise of return hole
            print('\n'+'This Hole does not even exist!')
            move_to_the_first_open_hole(model)
            model.switch_mode = False
            return False
        else:
            model.switch_pointer = Hole_index
            if model.assumptions[Hole_index-len(model.args)].value is not None:
                print('\n'+'you have already filled this hole')
                move_to_the_first_open_hole(model)
                model.switch_mode = False
                return False
            else:
                print(f"\nok you can now fill the {Hole_index}th Hole")
                #model.switch_mode = False
            return False
    except ValueError as e:
        print(f"{str(e)}")
    return False
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def fill_handler(command, model, fsm) -> bool:
    """ The user gives things like: fill: 4 , according to the hole he is filling, if he is not directed from switch, he will fill the first empty hole
            the type will be checked if type matches, then we accept to fill it with the desired value """
    try:
        res = fsm.check_and_advance(command, model)
        statement = command[len("fill:"):].strip()
        if fsm.given["intro_main"] == True and fsm.given["intro"] == True:
            #is there any local_variable so we can fill him?
            if len(model.assumptions_names_list) >= len(model.statements):
                res = save_assumptions(statement, model)
            else:
                print("no local variable to be given any value!")
                fsm.state = "FILL"
                return False
            if res == True:
                model.update_return_field(); model.update_holes_index()
                print("\n", model, sep="")
                fsm.state = "FILL"
                if modus == "interaktiv":
                    fsm.given ["fill"] = True
                    print("An assumption is saved *_*")
                    if model.switch_mode == True:
                        model.switch_mode == False
                model.statements.append(next(
                    (var for var in reversed(model.assumptions) if var.temporary_value is not None),None))
            else:
                print("Assumption is not defined!")
                fsm.state = "INTRO"
                return False
        elif fsm.given["intro_main"] == False:
            fsm.state = "SIGNATURE"
            print("Give your main inputs firstly and then think about the Assumptions!")
            return False
        elif fsm.given["intro"] == False and fsm.given["intro_main"] == True:
            print("No local variable to be given any value!")
            fsm.state = "FINISH" if fsm.given['finish'] else "RETURN" if fsm.given['return'] else "INTRO_MAIN"
            return False           
    except ValueError as e:
        print(f"{str(e)}")
    return False
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def return_handler(command, model, fsm) -> bool:
    """ the user gives thing like: return: x+5 and if the type matches it will  be saved, and there will be no other chance to change it
        but if the type does not match, then the user will be given infinite chances """
    if fsm.state == "RETURN" or fsm.given['return'] == True:
        print("you have already given return expression!")
        return False
    try:
        res = fsm.check_and_advance(command, model)
        if fsm.given["intro_main"] == True:
            expression = command[len("return:"):].strip(); expression = expression.strip()
            rs = check_the_type(expression, model.return_type ,model)
            if rs:
                model.return_expression = expression
                fsm.given["return"] = True
                print("\n", model, sep="")
                fsm.state = "RETURN"
                if modus == "interaktiv":
                    print("return part is saved *_*")    
                    return False 
            else:                                 
                print("Invalid return-type")
                fsm.state = "FILL"
                return False
        else:
            print("No retutrn before the inputs!")
            fsm.state = "INTRO_MAIN"
            return False
    except ValueError as e:
        print(f"{str(e)}")
        return False
    return False
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def finish_handler(command, model, fsm) -> bool:
    """ when the user gives: finish: and all important commands are given correctly and every hole is filled with the right type -> end the program successfully """
    try:
        resi = True
        res = fsm.check_and_advance(command, model)
        #we can't end when there is still some open holes
        #we have this complex rules, becausew of the return hole in the statements if nothing is in statements
        if model.assumptions:
            #if len (model.assumptions) + 1 == len(model.statements) or not len (model.assumptions) == len(model.statements) or\
            if any(var.value == None for var in model.assumptions):
                print("you can not leave open holes behind you!")
                fsm.state = "FILL"
                return False
        if model.return_expression is None:
            print("Your program is not complete, you have not given any valid return expression!")
            fsm.state = "FILL"
            return False
        resi = True
        fsm.given["finish"] = True
        print("\n", model, sep="")
        print("\n")
        return True
    except ValueError as e:
        print(f"{str(e)}")
        return False
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def tactic_interpreter(command, model, fms):
    """ The function for handling the commands through the helper function tactic_interpreter_main"""
    if type(command) == list:
        for item in command:
            tactic_interpreter_main(item, model,fms)
    else:
        tactic_interpreter_main(command, model,fms)
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def tactic_interpreter_main(command, model, fms):
    """ Helper function for tactic_interpreter, it handles all commands """ 
    if command.startswith("description:"):
        return description_handler(command, model, fms)
    
    elif command.startswith("signature:"):
        return signature_handler(command,model, fms)

    elif command.startswith("intro:"):  
        return intro_handler(command,model, fms)

    elif command.startswith("let:"):  
        return let_handler(command,model, fms)

    elif command.startswith("fill:"):
        return fill_handler(command,model, fms)

    elif command.startswith("switch:"):
        return switch_handler(command,model, fms)

    elif command.startswith("return:"):
        return return_handler(command,model, fms)

    elif command.startswith("finish:"):
        return finish_handler(command,model, fms)
    else:
        if fms.given["finish"] == True:
            print('Bye Bye')
        else:
            print("I think you have typerror!")
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def tutor_loop():
    """ The main function of the program, it takes inputs from user, decides in which mode are we, give command to process_tactic
        which reads command and together with tactic_interpreter they handle all the commands """
    model = ProgramModel()
    fms = CommandFSM(model)
    print("Gib einen Befehl ein:  ")
    command = input("").strip()
    global modus
    if command.endswith(".txt"):
        modus = "file_reading"
        while parser.process_tactic_helper(command, model, fms, tactic_interpreter) == False:
            parser.process_tactic_helper(command, model, fms, tactic_interpreter)       
    else:
        modus = "interaktiv"
        #for the first line
        if parser.process_tactic(command, model, fms, tactic_interpreter):
            return
        counter = 0
        while True:
            commandi = input("").strip()
            parser.process_tactic(commandi, model, fms, tactic_interpreter)
            if commandi == "":
                counter += 1
            if counter == 1:
                break
    return
tutor_loop()
