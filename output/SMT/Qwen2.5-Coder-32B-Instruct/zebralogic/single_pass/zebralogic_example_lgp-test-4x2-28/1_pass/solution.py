from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each house
house1_name = String('house1_name')
house2_name = String('house2_name')
house3_name = String('house3_name')
house4_name = String('house4_name')

house1_haircolor = String('house1_haircolor')
house2_haircolor = String('house2_haircolor')
house3_haircolor = String('house3_haircolor')
house4_haircolor = String('house4_haircolor')

# Define the domain for names and hair colors
names = ['Alice', 'Arnold', 'Peter', 'Eric']
hair_colors = ['black', 'blonde', 'brown', 'red']

# Add constraints for unique names and hair colors per house
solver.add(Distinct(house1_name, house2_name, house3_name, house4_name))
solver.add(Distinct(house1_haircolor, house2_haircolor, house3_haircolor, house4_haircolor))

# Add constraints based on the clues
# Clue 1: Eric is directly left of the person who has blonde hair.
solver.add(Or(
    And(house1_name == 'Eric', house2_haircolor == 'blonde'),
    And(house2_name == 'Eric', house3_haircolor == 'blonde'),
    And(house3_name == 'Eric', house4_haircolor == 'blonde')
))

# Clue 2: Alice and Arnold are next to each other.
solver.add(Or(
    And(house1_name == 'Alice', house2_name == 'Arnold'),
    And(house2_name == 'Alice', house1_name == 'Arnold'),
    And(house2_name == 'Alice', house3_name == 'Arnold'),
    And(house3_name == 'Alice', house2_name == 'Arnold'),
    And(house3_name == 'Alice', house4_name == 'Arnold'),
    And(house4_name == 'Alice', house3_name == 'Arnold')
))

# Clue 3: Eric is the person who has brown hair.
solver.add(house1_name != 'Eric', house2_name != 'Eric', house3_name != 'Eric', house4_name != 'Eric')
solver.add(Or(
    And(house1_name == 'Eric', house1_haircolor == 'brown'),
    And(house2_name == 'Eric', house2_haircolor == 'brown'),
    And(house3_name == 'Eric', house3_haircolor == 'brown'),
    And(house4_name == 'Eric', house4_haircolor == 'brown')
))

# Clue 4: The person who has black hair is not in the first house.
solver.add(house1_haircolor != 'black')

# Clue 5: Alice is in the first house.
solver.add(house1_name == 'Alice')

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HairColor"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_haircolor].as_string()],
                ["2", model[house2_name].as_string(), model[house2_haircolor].as_string()],
                ["3", model[house3_name].as_string(), model[house3_haircolor].as_string()],
                ["4", model[house4_name].as_string(), model[house4_haircolor].as_string()]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")