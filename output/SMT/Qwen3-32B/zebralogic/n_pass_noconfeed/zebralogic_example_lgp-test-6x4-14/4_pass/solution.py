from z3 import *

# Initialize the solver
solver = Solver()

# Define Z3 variables (for example, three integer variables representing categories)
category = {
    'event1': Int('category_event1'),
    'event2': Int('category_event2'),
    'event3': Int('category_event3'),
}

# Add the constraint that all category values must be distinct
solver.add(Distinct(*category.values()))

# Check if the constraints are satisfiable
result = solver.check()
if result == sat:
    model = solver.model()
    print("Model found:")
    for event, var in category.items():
        print(f"{event} -> {model[var]}")
else:
    print("No solution found.")