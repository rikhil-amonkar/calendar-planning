from z3 import *

# Create variables for each characteristic of each person
name = [String('name_%d' % i) for i in range(2)]
mother = [String('mother_%d' % i) for i in range(2)]
car_model = [String('car_model_%d' % i) for i in range(2)]
height = [String('height_%d' % i) for i in range(2)]

# Define the domain of possible values for each variable
names = ['Eric', 'Arnold']
mothers = ['Aniya', 'Holly']
car_models = ['ford f150', 'tesla model 3']
heights = ['short', 'very short']

# Create a solver instance
solver = Solver()

# Add constraints for unique values within each category
solver.add(Distinct(name))
solver.add(Distinct(mother))
solver.add(Distinct(car_model))
solver.add(Distinct(height))

# Add specific clues as constraints
# Clue 1: The person who owns a Tesla Model 3 is somewhere to the right of Arnold.
solver.add(Implies(car_model[1] == 'tesla model 3', name[0] != 'Arnold'))
solver.add(Implies(car_model[0] == 'tesla model 3', name[1] == 'Arnold'))

# Clue 2: Arnold is the person who is short.
solver.add(Implies(name[0] == 'Arnold', height[0] == 'short'))
solver.add(Implies(name[1] == 'Arnold', height[1] == 'short'))

# Clue 3: The person whose mother's name is Holly is in the second house.
solver.add(mother[1] == 'Holly')

# Solve the problem
if solver.check() == sat:
    m = solver.model()
    # Extract the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "CarModel", "Height"],
            "rows": [
                ["1", m[name[0]].as_string()[1:-1], m[mother[0]].as_string()[1:-1], m[car_model[0]].as_string()[1:-1], m[height[0]].as_string()[1:-1]],
                ["2", m[name[1]].as_string()[1:-1], m[mother[1]].as_string()[1:-1], m[car_model[1]].as_string()[1:-1], m[height[1]].as_string()[1:-1]]
            ]
        }
    }
    print(json.dumps(solution, indent=4))
else:
    print("No solution found")