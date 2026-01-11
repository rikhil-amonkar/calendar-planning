from z3 import *

# Create variables for the problem
person1 = String('person1')
person2 = String('person2')
vacation1 = String('vacation1')
vacation2 = String('vacation2')

# Define the domain for the variables
people = ['Arnold', 'Eric']
vacations = ['beach', 'mountain']

# Create a solver instance
solver = Solver()

# Add constraints based on the problem statement
# Each house must be occupied by a different person
solver.add(person1 != person2)

# Each person must be assigned to one of the two houses
solver.add(Or(person1 == 'Arnold', person1 == 'Eric'))
solver.add(Or(person2 == 'Arnold', person2 == 'Eric'))

# Each house must have a unique vacation preference
solver.add(vacation1 != vacation2)

# Each vacation must be assigned to one of the two houses
solver.add(Or(vacation1 == 'beach', vacation1 == 'mountain'))
solver.add(Or(vacation2 == 'beach', vacation2 == 'mountain'))

# Apply the clue: Arnold is somewhere to the right of the person who loves beach vacations
solver.add(Implies(vacation1 == 'beach', person2 == 'Arnold'))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    # Extract the solution
    solution_person1 = model.evaluate(person1).as_string()[1:-1]  # Remove quotes
    solution_vacation1 = model.evaluate(vacation1).as_string()[1:-1]  # Remove quotes
    solution_person2 = model.evaluate(person2).as_string()[1:-1]  # Remove quotes
    solution_vacation2 = model.evaluate(vacation2).as_string()[1:-1]  # Remove quotes
    
    # Format the solution as JSON
    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": [
                ["1", solution_person1, solution_vacation1],
                ["2", solution_person2, solution_vacation2]
            ]
        }
    }
    
    print(solution)
else:
    print("No solution found")