from z3 import *

def find_initial_conditions(equations, variables, input_vars, output_vars):
    # Suppress Z3 output to avoid issues with standard streams
    set_param('verbose', 0)
    set_param('smt.verbose', 0)
    
    # Create a solver instance without specifying a logic to avoid potential issues
    solver = Solver()
    
    # Create Z3 variables with appropriate types
    z3_vars = {}
    for name, var_type in variables.items():
        if var_type == "int":
            z3_vars[name] = Int(name)
        elif var_type == "float":
            z3_vars[name] = Real(name)
    
    # Add equations to the solver
    for eq in equations:
        solver.add(eval(eq, globals(), z3_vars))
    
    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()
        result = {}
        for name in variables:
            var = z3_vars[name]
            if variables[name] == "int":
                # Extract integer value
                result[name] = model[var].as_long()
            else:
                # Extract real value as float
                val = model[var]
                if is_rational_value(val):
                    # Convert rational to float
                    result[name] = float(val.numerator_as_long()) / float(val.denominator_as_long())
                else:
                    # Fallback for non-rational values (approximate)
                    result[name] = float(val.approx(10).as_fraction())
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
    print(result)