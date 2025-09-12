from z3 import *

# Define the variables
names = ['Eric', 'Peter', 'Arnold']
mothers = ['Holly', 'Aniya', 'Janelle']
foods = ['pizza', 'grilled cheese', 'spaghetti']

# Create a solver instance
solver = Solver()

# Create variables for each house
house1_name_sort, (eric, peter, arnold) = EnumSort('house1_name', names)
house2_name_sort, (eric2, peter2, arnold2) = EnumSort('house2_name', names)
house3_name_sort, (eric3, peter3, arnold3) = EnumSort('house3_name', names)

house1_mother_sort, (holly, aniya, janelle) = EnumSort('house1_mother', mothers)
house2_mother_sort, (holly2, aniya2, janelle2) = EnumSort('house2_mother', mothers)
house3_mother_sort, (holly3, aniya3, janelle3) = EnumSort('house3_mother', mothers)

house1_food_sort, (pizza, grilled_cheese, spaghetti) = EnumSort('house1_food', foods)
house2_food_sort, (pizza2, grilled_cheese2, spaghetti2) = EnumSort('house2_food', foods)
house3_food_sort, (pizza3, grilled_cheese3, spaghetti3) = EnumSort('house3_food', foods)

# Create variables for each house
house1_name = Const('house1_name', house1_name_sort)
house2_name = Const('house2_name', house2_name_sort)
house3_name = Const('house3_name', house3_name_sort)

house1_mother = Const('house1_mother', house1_mother_sort)
house2_mother = Const('house2_mother', house2_mother_sort)
house3_mother = Const('house3_mother', house3_mother_sort)

house1_food = Const('house1_food', house1_food_sort)
house2_food = Const('house2_food', house2_food_sort)
house3_food = Const('house3_food', house3_food_sort)

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
        return var.name().split('!')[1] if var.arity() == 0 else var
    
    # Extract the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "Food"],
            "rows": [
                ["1", get_value(model[house1_name]), get_value(model[house1_mother]), get_value(model[house1_food])],
                ["2", get_value(model[house2_name]), get_value(model[house2_mother]), get_value(model[house2_food])],
                ["3", get_value(model[house3_name]), get_value(model[house3_mother]), get_value(model[house3_food])]
            ]
        }
    }
    
    # Print the solution as JSON
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")