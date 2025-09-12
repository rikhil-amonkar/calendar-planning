from z3 import *
import json

# Define the variables
names = ['Eric', 'Peter', 'Arnold']
mothers = ['Holly', 'Aniya', 'Janelle']
foods = ['pizza', 'grilled cheese', 'spaghetti']

# Create a solver instance
solver = Solver()

# Create variables for each house
house1_name = EnumSort('house1_name', names)[0]
house2_name = EnumSort('house2_name', names)[0]
house3_name = EnumSort('house3_name', names)[0]

house1_mother = EnumSort('house1_mother', mothers)[0]
house2_mother = EnumSort('house2_mother', mothers)[0]
house3_mother = EnumSort('house3_mother', mothers)[0]

house1_food = EnumSort('house1_food', foods)[0]
house2_food = EnumSort('house2_food', foods)[0]
house3_food = EnumSort('house3_food', foods)[0]

# Add constraints for unique names, mothers, and foods
solver.add(Distinct(house1_name, house2_name, house3_name))
solver.add(Distinct(house1_mother, house2_mother, house3_mother))
solver.add(Distinct(house1_food, house2_food, house3_food))

# Add clues as constraints
# Clue 1: The person who loves the spaghetti eater and Peter are next to each other.
solver.add(Or(
    And(house1_food == 'spaghetti', house2_name == 'Peter'),
    And(house2_food == 'spaghetti', Or(house1_name == 'Peter', house3_name == 'Peter')),
    And(house3_food == 'spaghetti', house2_name == 'Peter')
))

# Clue 2: The person who loves eating grilled cheese is directly left of The person whose mother's name is Aniya.
solver.add(Or(
    And(house1_food == 'grilled cheese', house2_mother == 'Aniya'),
    And(house2_food == 'grilled cheese', house3_mother == 'Aniya')
))

# Clue 3: The person who loves eating grilled cheese is Eric.
solver.add(Or(
    house1_food == 'grilled cheese' == house1_name,
    house2_food == 'grilled cheese' == house2_name,
    house3_food == 'grilled cheese' == house3_name
))

# Clue 4: Peter is The person whose mother's name is Holly.
solver.add(Or(
    And(house1_name == 'Peter', house1_mother == 'Holly'),
    And(house2_name == 'Peter', house2_mother == 'Holly'),
    And(house3_name == 'Peter', house3_mother == 'Holly')
))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    
    # Extract the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "Food"],
            "rows": [
                ["1", str(model[house1_name]), str(model[house1_mother]), str(model[house1_food])],
                ["2", str(model[house2_name]), str(model[house2_mother]), str(model[house2_food])],
                ["3", str(model[house3_name]), str(model[house3_mother]), str(model[house3_food])]
            ]
        }
    }
    
    # Print the solution as JSON
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")