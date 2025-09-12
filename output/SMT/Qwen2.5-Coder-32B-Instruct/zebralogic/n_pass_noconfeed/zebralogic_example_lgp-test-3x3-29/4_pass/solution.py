from z3 import *
import json

# Define the variables
names = ['Eric', 'Peter', 'Arnold']
mothers = ['Holly', 'Aniya', 'Janelle']
foods = ['pizza', 'grilled cheese', 'spaghetti']

# Create a solver instance
solver = Solver()

# Create enumerated sorts for names, mothers, and foods
house_name_sort, (eric, peter, arnold) = EnumSort('house_name', names)
house_mother_sort, (holly, aniya, janelle) = EnumSort('house_mother', mothers)
house_food_sort, (pizza, grilled_cheese, spaghetti) = EnumSort('house_food', foods)

# Create variables for each house
house1_name = Const('house1_name', house_name_sort)
house2_name = Const('house2_name', house_name_sort)
house3_name = Const('house3_name', house_name_sort)

house1_mother = Const('house1_mother', house_mother_sort)
house2_mother = Const('house2_mother', house_mother_sort)
house3_mother = Const('house3_mother', house_mother_sort)

house1_food = Const('house1_food', house_food_sort)
house2_food = Const('house2_food', house_food_sort)
house3_food = Const('house3_food', house_food_sort)

# Add constraints for unique names, mothers, and foods
solver.add(Distinct(house1_name, house2_name, house3_name))
solver.add(Distinct(house1_mother, house2_mother, house3_mother))
solver.add(Distinct(house1_food, house2_food, house3_food))

# Add clues as constraints
# Clue 1: The person who loves the spaghetti eater and Peter are next to each other.
solver.add(Or(
    And(house1_food == spaghetti, house2_name == peter),
    And(house2_food == spaghetti, Or(house1_name == peter, house3_name == peter)),
    And(house3_food == spaghetti, house2_name == peter)
))

# Clue 2: The person who loves eating grilled cheese is directly left of The person whose mother's name is Aniya.
solver.add(Or(
    And(house1_food == grilled_cheese, house2_mother == aniya),
    And(house2_food == grilled_cheese, house3_mother == aniya)
))

# Clue 3: The person who loves eating grilled cheese is Eric.
solver.add(Or(
    And(house1_food == grilled_cheese, house1_name == eric),
    And(house2_food == grilled_cheese, house2_name == eric),
    And(house3_food == grilled_cheese, house3_name == eric)
))

# Clue 4: Peter is The person whose mother's name is Holly.
solver.add(Or(
    And(house1_name == peter, house1_mother == holly),
    And(house2_name == peter, house2_mother == holly),
    And(house3_name == peter, house3_mother == holly)
))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    
    # Map the model values back to strings for printing
    def get_value(var):
        return str(model[var])  # Convert the model value to a string
    
    # Extract the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "Food"],
            "rows": [
                ["1", get_value(house1_name), get_value(house1_mother), get_value(house1_food)],
                ["2", get_value(house2_name), get_value(house2_mother), get_value(house2_food)],
                ["3", get_value(house3_name), get_value(house3_mother), get_value(house3_food)]
            ]
        }
    }
    
    # Print the solution as JSON
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")