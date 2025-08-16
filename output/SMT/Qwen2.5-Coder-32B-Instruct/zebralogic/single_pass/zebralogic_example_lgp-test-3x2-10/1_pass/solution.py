from z3 import *

# Create variables for each characteristic of each house
house1_name = String('house1_name')
house2_name = String('house2_name')
house3_name = String('house3_name')

house1_height = String('house1_height')
house2_height = String('house2_height')
house3_height = String('house3_height')

# Define the domain for each variable
names = ['Eric', 'Arnold', 'Peter']
heights = ['short', 'very short', 'average']

# Create a solver instance
solver = Solver()

# Add constraints for unique names and heights per house
solver.add(Distinct(house1_name, house2_name, house3_name))
solver.add(Distinct(house1_height, house2_height, house3_height))

# Add constraints based on the clues
# Clue 1: Eric is not in the first house.
solver.add(house1_name != 'Eric')

# Clue 2: The person who is very short is somewhere to the left of the person who is short.
solver.add(Or(And(house1_height == 'very short', Or(house2_height == 'short', house3_height == 'short')),
              And(house2_height == 'very short', house3_height == 'short')))

# Clue 3: The person who is very short is Eric.
solver.add(Or(And(house1_height == 'very short', house1_name == 'Eric'),
              And(house2_height == 'very short', house2_name == 'Eric'),
              And(house3_height == 'very short', house3_name == 'Eric')))

# Clue 4: Arnold is not in the first house.
solver.add(house1_name != 'Arnold')

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