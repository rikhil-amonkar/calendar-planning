from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
house_arnold = Int('house_arnold')
house_eric = Int('house_eric')
house_grilled_cheese = Int('house_grilled_cheese')
house_pizza = Int('house_pizza')
house_holly = Int('house_holly')
house_aniya = Int('house_aninya')

# Constraints based on the problem statement
# There are only two houses
solver.add(house_arnold >= 1)
solver.add(house_arnold <= 2)
solver.add(house_eric >= 1)
solver.add(house_eric <= 2)
solver.add(house_grilled_cheese >= 1)
solver.add(house_grilled_cheese <= 2)
solver.add(house_pizza >= 1)
solver.add(house_pizza <= 2)
solver.add(house_holly >= 1)
solver.add(house_holly <= 2)
solver.add(house_aniya >= 1)
solver.add(house_aniya <= 2)

# Each person has a unique house
solver.add(house_arnold != house_eric)

# Each food preference is in a unique house
solver.add(house_grilled_cheese != house_pizza)

# Each mother's name is in a unique house
solver.add(house_holly != house_aniya)

# Clue 1: The person who loves eating grilled cheese is directly left of the person who is a pizza lover.
solver.add(house_grilled_cheese + 1 == house_pizza)

# Clue 2: Arnold is not in the second house.
solver.add(house_arnold != 2)

# Clue 3: Arnold is The person whose mother's name is Holly.
solver.add(house_arnold == house_holly)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    house_arnold_value = model[house_arnold].as_long()
    house_eric_value = 3 - house_arnold_value  # Since there are only two houses and they are unique
    house_grilled_cheese_value = model[house_grilled_cheese].as_long()
    house_pizza_value = 3 - house_grilled_cheese_value  # Since there are only two houses and they are unique
    house_holly_value = model[house_holly].as_long()
    house_aniya_value = 3 - house_holly_value  # Since there are only two houses and they are unique

    # Determine the food and mother for each person
    if house_arnold_value == house_grilled_cheese_value:
        arnold_food = "grilled cheese"
        eric_food = "pizza"
    else:
        arnold_food = "pizza"
        eric_food = "grilled cheese"

    if house_holly_value == house_grilled_cheese_value:
        arnold_mother = "Holly"
        eric_mother = "Aniya"
    else:
        arnold_mother = "Aniya"
        eric_mother = "Holly"

    # Construct the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Food", "Mother"],
            "rows": [
                [str(house_arnold_value), "Arnold", arnold_food, arnold_mother],
                [str(house_eric_value), "Eric", eric_food, eric_mother]
            ]
        }
    }

    print(json.dumps(solution, indent=2))
else:
    print("No solution found")