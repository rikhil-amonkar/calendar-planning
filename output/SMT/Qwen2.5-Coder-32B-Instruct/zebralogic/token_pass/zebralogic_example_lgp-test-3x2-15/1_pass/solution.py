from z3 import *

# Define variables for names and heights
names = ['Arnold', 'Peter', 'Eric']
heights = ['short', 'average', 'very short']

# Create variables for each house
house1_name = String('house1_name')
house1_height = String('house1_height')
house2_name = String('house2_name')
house2_height = String('house2_height')
house3_name = String('house3_name')
house3_height = String('house3_height')

# Create a solver instance
solver = Solver()

# Add constraints for unique names and heights
solver.add(Distinct(house1_name, house2_name, house3_name))
solver.add(Distinct(house1_height, house2_height, house3_height))

# Add constraints based on the clues
# Clue 1: Peter is somewhere to the right of Eric
solver.add(Or(house2_name == 'Peter', house3_name == 'Peter'))
solver.add(Or(house1_name == 'Eric', house2_name == 'Eric'))

# Clue 2: The person who is short is in the first house
solver.add(house1_height == 'short')

# Clue 3: There is one house between the person who is short and the person who is very short
solver.add(house3_height == 'very short')

# Clue 4: Arnold and the person who is very short are next to each other
solver.add(house2_name == 'Arnold')

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_height].as_string()],
                ["2", model[house2_name].as_string(), model[house2_height].as_string()],
                ["3", model[house3_name].as_string(), model[house3_height].as_string()]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")