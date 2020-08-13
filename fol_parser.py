import z3
from lark import Lark, Token, Tree

# Should True and False be terms or formulas?
# Or should everything be just a term, and a formula is a boolean term?

grammar_string = '''
    start: program
    program: preamble logic query
    preamble: "Preamble" declaration+

    sort: "Sort"
    constant: "Constant"
    argumental: "Function"
    bound: "Bound"

    bools: "Boolean" | "B"
    ints: "Integer" | "Z"
    reals: "Real" | "R"

    builtin: bools
           | ints
           | reals

    type: (symbol | builtin)
        | (symbol | builtin) ("," (symbol | builtin))* "->" (symbol | builtin)

    declaration: constant symbols ":" (symbol | builtin) dot
               | sort symbols dot
               | argumental symbols ":" type dot
               | bound integral dot

    logic: "Logic" statement+

    letter: "a".."z"
    digit: "0".."9"
    digits: digit+

    lod: letter
       | digit

    symbol: letter+
          | letter lod+

    integral: digit+

    negation: "~"

    symbols: symbol
           | symbol "," symbols

    function: symbol "(" terms ")"

    term: true
        | false
        | symbol
        | function
        | integral
        | operation
        | "(" term ")"

    operation: term operator term

    terms: term
         | term "," terms

    some: "Some"
    all: "All"

    quantifier: some
              | all

    binding: quantifier symbols ":"

    implies: "=>"
    and: ","
    or: "|"

    connective: implies
              | and
              | or

    equal: "="
    notequal: "!="
    greater: ">"
    smaller: "<"

    comparison: equal
              | notequal
              | greater
              | smaller

    plus: "+"

    operator: plus

    true: "True"
    false: "False"

    formula: function
           | negation formula
           | term comparison term
           | formula connective formula
           | binding formula
           | "(" formula ")"

    dot: "."

    statement: formula dot

    query: "Query" request

    solve: "Solve"
    models: "Models"

    request: solve symbols dot
           | models symbols dot

    %import common.WS
    %ignore WS
'''


def show(tree, depth=0):
    '''
    Input: an ast
    Return: a string showing the elements in the tree,
    representing hierarchy with identation.
    '''
    to_show = ""
    if isinstance(tree, Token):
        print("  " * depth + str(tree))
    elif isinstance(tree, Tree):
        print("  " * depth + str(tree.data))
        for child in tree.children:
            show(child, depth+1)
    return to_show


def prefix_notation(tree):
    '''
    Input: a lark parse tree.
    Return: the same ast, but as nested lists in polish notation.
    '''
    as_list = []
    if isinstance(tree, Token):
        as_list.append(str(tree))
    elif isinstance(tree, Tree):
        as_list.append(str(tree.data))
        as_list = as_list + [prefix_notation(t) for t in tree.children]
    return as_list


# def execute(statements):
#    z3_solver = z3.Solver()
#    definitions = get_definitions(statements)
#    facts = add_facts(z3_solver, definitions, statements)
#    queries = get_queries(statements)
#    solve_queries(queries, z3_solver)


def handle_symbol(ast, state):
    '''
    Input: an ast and a state dictionary
    Return: a string with the terminal characters of the
    symbol node of the ast.

    Raises an error if the input ast does not have 'symbol'
    as its root.

    Remember to handle letters and digits
    '''
    if ast[0] == "symbol":
        output_string = ""
        for elem in ast[1:]:
            if elem[0] == 'letter':
                output_string = output_string + elem[1][0]
            elif elem[0] == 'lod':
                output_string = output_string + elem[1][1][0]
        return (output_string, state)
    else:
        raise RuntimeError(f'''Expected an ast node tagged with 'symbol', found {ast[0]}''')


def handle_integral(ast, state):
    integral = 0
    digits = []
    if ast[0] == 'integral':
        for digit in ast[1:]:
            digits.append(digit[1][0])
        digits = "".join(digits)
        integral = int(digits)
        return (integral, state)
    else:
        raise RuntimeError('''Expected 'digits', found '{ast[0]}' in
                               {ast}''')


def handle_symbols(ast, state):
    '''
    Input: an ast, and a state dictionary
    Return: a list of strings with the symbols in the ast.
    '''
    if ast[0] == 'symbol':
        return ([handle_symbol(ast, state)[0]], state)

    elif ast[0] == "symbols":
        symbols = []
        remainder = ast[1:]
        if len(remainder) == 1:
            symbol_tuple = handle_symbol(remainder[0], state)
            symbols = symbols + [symbol_tuple[0]]

        elif len(remainder) == 2:
            symbol_tuple = handle_symbol(remainder[0], state)
            symbols_tuple = handle_symbols(remainder[1], state)

            symbols = symbols + [symbol_tuple[0]] + symbols_tuple[0]

        else:
            raise RuntimeError(f''''Symbols' nodes are expected to have length 1 or 2, but
            the 'symbols' node in {ast} has length {len(ast[1:])}''')

        return (symbols, state)
 
    else:
        raise RuntimeError(f'''Expected an ast node tagged with 'symbols', found {ast[0]}
        in {ast}''')


def handle_binding(ast, state):
    '''
    Input: an ast and a state dictionary
    Return: a quantified formula and the same state
    '''
    if ast[0][0] == "binding":
        quantifier = ast[0][1][1][0]
        variables = handle_symbols(ast[0][2], state)[0]
        formula = handle_formula(ast[1], state)[0]
        if quantifier == 'all':
            return (z3.ForAll([state[v] for v in variables], formula), state)
        elif quantifier == 'some':
            return (z3.Exists([state[v] for v in variables], formula), state)
        else:
            raise RuntimeError(f"Expected a quantifier, found {quantifier}")
    else:
        raise RuntimeError(f'''Expected either 'Some <variables>' or
        'All <variables>', found {ast[0]} in {ast}''')


def handle_function(ast, state):
    function_name = handle_symbol(ast[1], state)[0]
    function_arguments = handle_terms(ast[2], state)[0]
    function = state[function_name](*function_arguments)
    return (function, state)


def handle_connective(ast, state):
    '''
    Input: a list of ast nodes [formula, connective, formula]
    Return: the formula (f1 * f2)
    '''
    if ast[1][0] == 'connective' and len(ast) == 3:

        left_formula = handle_formula(ast[0], state)[0]
        right_formula = handle_formula(ast[2], state)[0]
        connective = ast[1][1][0]

        if connective == 'implies':
            return (z3.Implies(left_formula, right_formula), state)
        elif connective == 'and':
            return (z3.And(left_formula, right_formula), state)
        elif connective == 'or':
            return (z3.Or(left_formula, right_formula), state)
        else:
            raise RuntimeError('''Expected 'implies', 'and' or 'or',
                               but found {connective} at {ast}''')
    else:
        raise RuntimeError('''Expected 'connective', found {ast[1][0]}
                               at {ast}''')


def handle_comparison(ast, state):
    '''
    Input: a list of ast nodes [term, comparison, term]
    Return: a formula consisting of the comparison of two terms
    '''

    left_term = handle_term(ast[0], state)[0]
    right_term = handle_term(ast[2], state)[0]

    if ast[1][0] == 'comparison' and ast[1][1][0] == 'equal':
        return (left_term == right_term, state)
    elif ast[1][0] == 'comparison' and ast[1][1][0] == 'notequal':
        return (left_term != right_term, state)
    elif ast[1][0] == 'comparison' and ast[1][1][0] == 'smaller':
        return (left_term < right_term, state)
    elif ast[1][0] == 'comparison' and ast[1][1][0] == 'greater':
        return (left_term > right_term, state)
    else:
        raise RuntimeError(f"Expected a 'comparison' node, but got {ast}")


def handle_operation(ast, state):
    if ast[0] == 'operation':
        left_term = handle_term(ast[1], state)[0]
        right_term = handle_term(ast[3], state)[0]

        if ast[2][1][0] == 'plus':
            return left_term + right_term
        else:
            raise RuntimeError('''Expected 'plus', found {ast[2][1][0]}
                                 in (ast[2])''')

    else:
        raise RuntimeError(f'''Expected a 'operation' node, found
        {ast[0]} in {ast}''')


def handle_negation(ast, state):
    if ast[0][0] == 'negation':
        return (z3.Not(handle_formula(ast[1], state)[0]), state)
    else:
        raise RuntimeError(f'''Expected 'negation', found {ast[0][0]}
                           at {ast}''')


def function_declaration(ast, state):
    '''
    Input: an ast containing a function declaration and a state dictionary.
    Output: a z3 function object, and the updated state, i.e.
    state[function_name] == function_object
    '''
    if ast[0][0] == 'argumental':
        function_names = handle_symbols(ast[1], state)[0]
        sorts = handle_type(ast[2], state)[0]

        for function_name in function_names:
            declaration_arguments = [function_name] + sorts
            state[function_name] = z3.Function(*declaration_arguments)
            state["Sorts"][function_name] = ("function", declaration_arguments[1:])
        return (function_name, state)
    else:
        raise RuntimeError(f'''Expected 'argumental', found '{ast[0][0]}'
        at {ast}''')


def constant_declaration(ast, state):
    '''
    Input: an ast with a root tagged 'constant'
    Return: a list with constant names, and the updated state
    '''

    if ast[0][0] == 'constant':

        constant_names = handle_symbols(ast[1], state)[0]

        if ast[2][0] == 'symbol':
            sort_name = handle_symbol(ast[2], state)[0]
        elif ast[2][0] == 'builtin':
            sort_name = handle_builtin(ast[2], state)[0]
        else:
            raise RuntimeError(f'''Expected 'symbol' or 'builtin', but
                               found {ast[2][0]} in {ast}''')
        
        for constant_name in constant_names:
            state[constant_name] = z3.Const(constant_name, state[sort_name])
            state["Sorts"][constant_name] = ("constant", state[sort_name])
        
        return (constant_name, state)
    
    else:
        raise RuntimeError('''Expected a 'constant' node,
        but found {ast[0]} in {ast}''')


def sort_declaration(ast, state):
    if ast[0][0] == 'sort':
        for sym in handle_symbols(ast[1], state)[0]:
            state[sym] = z3.DeclareSort(sym)
        return (ast, state)
    else:
        raise RuntimeError('''Expected a 'sort' node, found {ast[0]}
                           in {ast[1]}''')


def bound_declaration(ast, state):
    bound = 0
    if ast[0][0] == 'bound':
        bound = handle_integral(ast[1], state)[0]
    state["Bound"] = bound
    return (bound, state)


def handle_term(ast, state):
    '''
    Input: a ast containing a term description and a state dictionary
    Return: the z3 object corresponding to the term, and the state
    '''
    # The case where the term is a single term between parentheses
    # probably overlaps with others

    if ast[0] == 'term' and ast[1][0] == 'symbol':
        sym = handle_symbol(ast[1], state)[0]
        return (state[sym], state)

    elif ast[0] == 'term' and ast[1][0] == 'function':
        return handle_function(ast[1], state)

    elif ast[0] == 'term' and ast[1][0] == 'integral':
        return handle_integral(ast[1], state)

    elif ast[0] == 'term' and ast[1][0] in ['true', 'false']:
        return (state[ast[1][0]], state)

    elif ast[0] == 'term' and ast[1][0] == 'operation':
        return handle_operation(ast[1], state)

    elif ast[0] == 'term' and ast[1][0] == 'term':
        return handle_term(ast[1], state)
        
    else:
        raise RuntimeError(f'''Expected 'term', found {ast[0]} in {ast}''')


def handle_terms(ast, state):
    if ast[0] == 'term':
        return ([handle_term(ast, state)[0]], state)

    elif ast[0] == "terms":
        symbols = []
        remainder = ast[1:]
        if len(remainder) == 1:
            symbol_tuple = handle_term(remainder[0], state)
            symbols = symbols + [symbol_tuple[0]]
  
        elif len(remainder) == 2:
            symbol_tuple = handle_term(remainder[0], state)
            symbols_tuple = handle_terms(remainder[1], state)
  
            symbols = symbols + [symbol_tuple[0]] + symbols_tuple[0]
  
        else:
            raise RuntimeError(f''''terms' nodes are expected to have length 1 or 2, but
            the 'terms' node in {ast} has length {len(ast[1:])}''')
  
        return (symbols, state)

    else:
        raise RuntimeError(f'''Expected an ast node tagged with 'symbols', found {ast[0]}
        in {ast}''')


def handle_output_type(ast, state):
    '''
    Input: an ast and a state.
    Return: a string with the name of the sort, together with the state.
    '''
    if ast[0] == 'builtin':
        if ast[1][0] == 'bools':
            return ("B", state)
        elif ast[1][0] == 'ints':
            return ("Z", state)
        else:
            raise RuntimeError(f'''Expected 'bools' or 'ints', found
                               {ast[0]} in {ast}''')

    elif ast[0] == 'symbol':
        return (handle_symbol(ast, state)[0], state)
    
    else:
        raise RuntimeError(f'''Expected either 'builtin' or 'symbol', but found
                           {ast[0]} in {ast}''')


def handle_builtin(ast, state):
    if ast[0] == 'builtin':
        if ast[1][0] == 'bools':
            builtin_sort_name = "B"
        elif ast[1][0] == 'ints':
            builtin_sort_name = "Z"
        elif ast[1][0] == 'reals':
            builtin_sort_name = "R"
        else:
            raise RuntimeError("Expected a builtin sort.")
        return (builtin_sort_name, state)
    else:
        raise RuntimeError('''Expected 'builtin', found {ast[0]} in
                           {ast}''')


def handle_type(ast, state):
    '''
    Input: an ast and a sate
    Output: a tuple of z3 sorts and the same state
    '''
    if ast[0] == 'type':
        types = []
        remainder = ast[1:]
        for rem in remainder:
            if rem[0] == 'symbol':
                types.append(handle_symbol(rem, state)[0])
            elif rem[0] == 'builtin':
                types.append(handle_builtin(rem, state)[0])
            else:
                raise RuntimeError(f'''Expected either 'symbol' or 'builtin', but
                    found {rem[0]} at {rem} in {ast}.''')
        types = [state[t] for t in types]
        return (types, state)
    else:
        raise RuntimeError(f'''Expected a 'type' node, found '{ast[0]}'
                           at {ast}''')


def handle_declaration(ast, state):
    if ast[0] == 'declaration':
        declaration, new_state = handle_declaration(ast[1:], state)
        return declaration, new_state
    elif ast[0][0] == 'constant':
        declaration, new_state = constant_declaration(ast, state)
        return declaration, new_state
    elif ast[0][0] == 'argumental':
        declaration, new_state = function_declaration(ast, state)
        return declaration, new_state
    elif ast[0][0] == 'sort':
        declaration, new_state = sort_declaration(ast, state)
        return declaration, new_state
    elif ast[0][0] == 'bound':
        declaration, new_state = bound_declaration(ast, state)
        return declaration, new_state
    else:
        raise RuntimeError(f'''Expected either 'Bound', 'Constant',
        'Function' or 'Sort', but found {ast[0]} in {ast}''')


def handle_declarations(ast, state):
    if ast[0] == "preamble":
        declarations = []
        new_state = state
        remaining_declarations = ast[1:]
        for d in remaining_declarations:
            new_declaration, new_state = handle_declaration(d, new_state)
            declarations.append(new_declaration)
        return (declarations, new_state)
    else:
        raise RuntimeError(f'''Expected 'preamble', instead found
        {ast[0]} in {ast}''')


def handle_logic(ast, state):
    if ast[0] == 'logic':
        rules = []
        new_state = state
        remaining_rules = ast[1:]
        for r in remaining_rules:
            new_rule, new_state = handle_formula(r, new_state)
            rules.append(new_rule)
        return (rules, new_state)

    else:
        raise RuntimeError('''Expected a 'logic' node, got {ast[0]}
                           in {ast}''')


def single_term_formula(ast, state):
    if ast[0] == 'formula':
        formula = handle_formula(ast, state)[0]
    elif ast[0] == 'function':
        formula = handle_function(ast, state)[0]
    else:
        raise RuntimeError(f'''Expected either formula or function, but found
                             {ast[0]} at {ast}''')
    return (formula, state)


def two_term_formula(ast, state):
    if ast[0][0] == 'negation':
        print(ast)
        formula = z3.Not(handle_formula(ast[1], state)[0])
    elif ast[0][0] == 'binding':
        formula = handle_binding(ast, state)[0]
    else:
        raise RuntimeError(f'''Expected either negation or binding, found
                            {ast[0][0]} in {ast[0]}''')
    return (formula, state)


def three_term_formula(ast, state):
    if ast[1][0] == 'comparison':
        formula = handle_comparison(ast, state)[0]
    elif ast[1][0] == 'connective':
        formula = handle_connective(ast, state)[0]
    else:
        raise RuntimeError(f'''Expected either 'comparison' or 'connective',
                            but found {ast[1][0]} at {ast[1]}, in
                            {ast}''')
    return (formula, state)


def handle_formula(ast, state):
    if ast[0] == 'statement':
        return handle_formula(ast[1], state)

    elif ast[0] == 'formula':
        arguments = ast[1:]

        if len(arguments) == 1:
            return single_term_formula(arguments[0], state)

        elif len(arguments) == 2:
            return two_term_formula(arguments, state)
        
        elif len(arguments) == 3:
            return three_term_formula(arguments, state)

        else:
            raise RuntimeError(f''''formula' nodes must have 1, 2 or 3 children.
                               This node had {len(arguments)} children.
                               The node looked like this: {ast}''')

    else:
        raise RuntimeError(f'''Expected a 'formula' ast node, found
                           {ast[0]} at {ast}''')

def handle_request(ast, state, solver):

    if ast[0] == 'request':
        if ast[1][0] == 'solve':
            requested_symbols = handle_symbols(ast[2], state)[0]
            requested_constants = [state[s] for s in requested_symbols]
            if solver.check() == z3.sat:
                for rc in requested_constants:
                    print(f"The value Z3 found for {rc} is: {solver.model()[rc]}")
            elif solver.check() == z3.unsat:
                print("Z3 found that the theory stored in the solver is not satisfiable!")
                print('''Hence, it has no models, and there are no values to show for any
                of the requested symbols.''')
            elif solver.check() == z3.unknown:
                print('''Z3 could not find any model for the theory stored in the solver,
                      but the theory was not determined to be unsatisfiable either.''')

        elif ast[1][0] == 'models':
            requested_symbols = handle_symbols(ast[2], state)[0]
            requested_constants = [state[s] for s in requested_symbols] # falta registrar el sort
            rc = requested_constants[0]
            print(rc)
            counter = 0
            looking_for_models = True
            while looking_for_models:
                if solver.check() == z3.sat:
                    current_reference = solver.model()[rc]
                    print(current_reference)
                    solver.add(rc != current_reference)
                    counter += 1
                    looking_for_models = looking_for_models and counter < state["Bound"]
                elif solver.check() == z3.unsat:
                    print("From here on, the theory becomes unsatisfiable.")
                    looking_for_models = False
                elif solver.check not in [z3.sat, z3.unsat]:
                    print("Z3 could not determine if the theory is satisfiable or not")
                    looking_for_models = False
        else:
            raise RuntimeError(f'''Expected either 'models' or 'solve', found {ast[1][0]}''')

    else:
        raise RuntimeError(f'''Expected a 'request' node,
                           found {ast[0]} in {ast}''')


def handle_program(ast):
    if ast[0] == "start":
        return handle_program(ast[1])
    elif ast[0] == "program":
        state = initialize_state()
        solver = z3.Solver()
        declarations, state = handle_declarations(ast[1], state)
        rules, state = handle_logic(ast[2], state)
        print("Rules:")
        for rule in rules:
            print(rule)
            solver.add(rule)
        print("")
        handle_request(ast[3][1], state, solver)
        return (solver, state)
    else:
        raise RuntimeError(f'''Expected either 'program' or 'start',
        found {ast[0]} in {ast}''')


def initialize_state():
    state = {}
    state["true"] = True
    state["false"] = False
    state["Z"] = z3.IntSort()
    state["B"] = z3.BoolSort()
    state["R"] = z3.RealSort()
    state["Bound"] = 5
    state["Sorts"] = {}
    return state


lark_parser = Lark(grammar_string)

test_string = '''
    Preamble
        Sort node.
        Function f, g, h, i: B, B -> B.
        Constant a, b, c, d: B.

    Logic
        All a, b: a != b => f(a, b) = True.
        All a, b: (Some c: f(a, b) = g(c, b)).
        All a, b: g(a, b) != h(a, b).

    Query
        Solve f, g, h, i.
'''

statements = lark_parser.parse(test_string)
pref = prefix_notation(statements)
sl, st = handle_program(pref)
print("")
