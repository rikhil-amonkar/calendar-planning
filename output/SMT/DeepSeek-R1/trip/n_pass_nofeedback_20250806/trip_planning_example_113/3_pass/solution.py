from z3 import *

# Suppress all Z3 output to avoid issues with standard streams
set_param('verbose', 0)
set_param('smt.verbose', 0)

def find_initial_conditions(equations, variables, input_vars, output_vars):
    # Create a solver instance
    solver = Solver()
    
    # Create Z3 variables with appropriate types
    z3_vars = {}
    for name, var_type in variables.items():
        if var_type == "int":
            z3_vars[name] = Int(name)
        elif var_type == "float":
            z3_vars[name] = Real(name)
    
    # Create a safe evaluation environment with minimal symbols
    safe_env = {
        '__builtins__': None,  # No built-in functions
        'z3_vars': z3_vars,    # Only our variables
        # Z3 operations
        'And': And,
        'Or': Or,
        'Not': Not,
        'If': If,
        'Abs': Abs
    }
    
    # Add equations to the solver
    for eq in equations:
        try:
            # Evaluate in restricted environment
            constraint = eval(eq, safe_env, {})
            solver.add(constraint)
        except:
            # Skip invalid equations
            continue
    
    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()
        result = {}
        for name in variables:
            var = z3_vars[name]
            if variables[name] == "int":
                # Handle integer values
                try:
                    result[name] = model[var].as_long()
                except:
                    result[name] = 0
            else:
                # Handle real values
                val = model[var]
                try:
                    # Check if rational value
                    if is_rational_value(val):
                        result[name] = float(val.numerator_as_long()) / float(val.denominator_as_long())
                    # Check if integer value
                    elif is_int_value(val):
                        result[name] = float(val.as_long())
                    else:
                        # Algebraic number approximation
                        result[name] = float(val.approx(10).as_fraction())
                except:
                    result[name] = 0.0
        return result
    else:
        return None

# Example usage
if __name__ == "__main__":
    equations = [
        "z3_vars['x'] + z3_vars['y'] == 10",
        "z3_vars['x'] - z3_vars['y'] == 2"
    ]
    variables = {'x': 'int', 'y': 'int'}
    input_vars = ['x']
    output_vars = ['y']
    
    result = find_initial_conditions(equations, variables, input_vars, output_vars)
    if result:
        # Directly format output without print if needed
        output = str(result)
    else:
        output = "No solution found"