from data_model import ProgramModel, Variable, Type, IntType, FloatType, ComplexType, StrType, BoolType
import re, keyword
basic_types = {"int", "bool", "str", "float", "complex"}
#The following 5 functions concern about the signature ↓

def is_valid_name(name: str) -> bool:
    return name.isidentifier() and not keyword.iskeyword(name)

def split_top_level_commas(s) -> list[str]:
    """" help function for complex signature, which looks at every separated input even when it is complex, e.g:
        split_top_level_commas('int, float, ((bool, bool)->bool)') -> ['int', 'float', '((bool, bool)->bool)']"""
    parts = []
    current = ''
    depth = 0
    for c in s:
        if c == '(':
            depth += 1
            current += c
        elif c == ')':
            depth -= 1
            current += c
        elif c == ',' and depth ==0:
            parts.append(current.strip())
            current = ''
        else:
            current += c
    if current.strip():
        parts.append(current.strip() )
    return parts

def parse_type(s) -> bool:
    """" The function which checks wether the signature is right, e.g:
        parse_type('(int, str) -> int') -> True """
    s = s.strip()
    #see if it is of basic type, (do not care about having basic type string only as signature
    #it will be prevented in another function in signature that it stands alone as basic type
    if s in basic_types:
        return True
    #signature with one input? -> it is ok to not have () around the input
    if '->' in s and not s.startswith('('):
        left, right = s.split('->',1)
        param = left.strip()
        ret = right.strip()
        if parse_type(param) and parse_type(ret):
            return True
        else:
            return False
    # check if, if function type with parenthesis:(..)->....
    if s.startswith('('):
        #Find approperiate ')'
        depth = 0
        for i, c in enumerate(s):
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
                if depth ==0:
                    break
        else:
            return False  #No closing parenthesis

        param_part = s[1:i].strip()
        if (param_part.strip()).endswith(','):
            return False
        rest = s[i+1:].strip()

        if not rest.startswith('->'):
            return False

        ret_part = rest[2:].strip()
        params = split_top_level_commas(param_part)
        
        if len(params) == 1 and params[0] == '':
            params = []
        for p in params:
            if not parse_type(p):
                return False
        if not parse_type(ret_part):
            return False
        return True
    return False
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def extract_direct_types(signature_without_name:str, model) -> bool:
    """ If this function says True, It will extract all the types extracted from signature, and fill it in model.args """
    if not parse_type(signature_without_name):
        raise ValueError("Invalid signature!")
        return
    signature = signature_without_name.strip()
    #firstly: Find the top-level '->' (outside of parentheses)"
    depth = 0
    arrow_index = -1
    for i in range(len(signature)):
        if signature[i] == '(':
            depth += 1
        elif signature[i] == ')':
            depth -= 1
        elif signature[i:i+2] == '->' and depth == 0:
            arrow_index = i
            break
    typess = []
    if arrow_index == -1:
        raise ValueError("No valid top-level '->' found! The signature has not the right format")
        return
    left_part = signature[:arrow_index].strip()
    #If more than one Argument, then grouped with ()
    if left_part.strip() in basic_types:
        typess = [left_part.strip()]
    elif left_part.startswith('(') and left_part.endswith(')'):
        left_part = left_part[1:-1].strip()
        #
        typess = [x.strip() for x in left_part.split(",") if x.strip() != "" and not bool(re.fullmatch(r'\s*\(\s*\)\s*', x))]
    for i in range(len(typess)):
        model.args.append(Variable.InputArgument(typess[i], typess[i]))
    return True
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def split_on_last_arrow(s) -> tuple[str, str]:
    """ A fucntion that will split the full type_part of signature into args and return_type
        split_on_last_arrow('(int, str, bool) -> int') -> ('(int, str, bool) ', ' int')"""
    depth = 0
    if "[" in s:
        for i in range(len(s)- 2, -1, -1):
            if s[i] == ']':
                depth += 1
            elif s[i] == '[':
                depth -= 1
            elif s[i:i+2] == '->' and depth == 0:
                return s[:i], s[i+2: ]
    else:
        for i in range(len(s) - 2, -1, -1):
            if s[i] == ')':
                depth += 1
            elif s[i] == '(':
                depth -= 1
            elif s[i:i+2] == '->' and depth == 0:
                return s[:i],s[i+2:]
    return s,''
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def process_tactic_helper(command,model, fms, tactic_interpreter_func):
    """ This function takes the input_commands from the user and give it at the end to tactic_interpreter function to handle them.
        This process in this function is done in file_reading_mode """
    if command.endswith(".txt"):
        commands = ["signature", "description", "testing", "intro", "assume", "return", "finish"]
        blocks = []            # Sorted list of all commands blocks
        current_block = []     # Current block (List of lines)
        current_command = None # Current command
        with open(command, "r", encoding="utf-8") as file:
            for line in file:
                stripped = line.strip()
                # Check if line starts with one of the commands
                found_command = next((cmd for cmd in commands if stripped.startswith(cmd)), None)

                if found_command:
                    #Start a new block (save the old one, if available)
                    if current_block:
                        blocks.append(current_block)
                    current_block = [stripped]
                    current_command = found_command
                else:
                    #line belongs to the current block (if there is open one)
                    if current_command:
                        current_block.append(stripped)

            #Do not forget the last block
            if current_block:
                blocks.append(current_block)
            flat_blocks = [line for block in blocks for line in block]
            ress = []
            current_group = []

            for item in flat_blocks:
                if item.strip() == "":
                    if current_group:
                        ress.append(" ".join(current_group))
                        current_group = []
                    else:
                        #Empty lines but no previous group -> just pass
                        continue           
                else:
                    current_group.append(item)
            #if anything remains at the end
            if current_group:
                ress.append(" ".join(current_group))

            ress = [item for item in ress if item != ""]
    return tactic_interpreter_func(ress, model, fms)
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
def process_tactic(command, model, fms, tactic_interpreter_func):
    """ This  function does the same as process_tactic_helper but in the interactive mode """
    lines = []
    #Add the first line
    lines.append(command)
    while True:
        try:
            line = input()
        except EOFError:
            break
        #If the user just presses Enter (i.e., an empty line) -> exit
        if line.strip() == "":
            break
        #If the user adds more than one line at once(i.e., with copy_paste) -> check for duplicate line breaks
        split_lines = line.splitlines()
        if "" in [l.strip() for l in split_lines]:
            lines.extend(split_lines)
            break
        else:
            lines.append(line)
    #Merge all to one string
    full_command = "\n".join(lines)
    #Give it to tactic_interpreter
    return tactic_interpreter_func(full_command, model, fms)
#* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
