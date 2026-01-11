from z3 import Solver, Bool, And, Or, Not, sat

# Define variables
s = Solver()

# Variables for house assignments
eric_in_house_1 = Bool('eric_in_house_1')
arnold_in_house_1 = Bool('arnold_in_house_1')
eric_in_house_2 = Bool('eric_in_house_2')
arnold_in_house_2 = Bool('arnold_in_house_2')

# Variables for food assignments
eric_eats_pizza = Bool('eric_eats_pizza')
arnold_eats_pizza = Bool('arnold_eats_pizza')
eric_eats_grilled_cheese = Bool('eric_eats_grilled_cheese')
arnold_eats_grilled_cheese = Bool('arnold_eats_grilled_cheese')

# Constraints based on clues
# Clue 1: The person who is a pizza lover is in the second house.
s.add(Or(eric_eats_pizza == eric_in_house_2, arnold_eats_pizza == arnold_in_house_2))

# Clue 2: Arnold is not in the first house.
s.add(Not(arnold_in_house_1))

# Each person is in exactly one house
s.add(Or(eric_in_house_1, eric_in_house_2))
s.add(Not(And(eric_in_house_1, eric_in_house_2)))
s.add(Or(arnold_in_house_1, arnold_in_house_2))
s.add(Not(And(arnold_in_house_1, arnold_in_house_2)))

# Each person eats exactly one type of food
s.add(Or(eric_eats_pizza, eric_eats_grilled_cheese))
s.add(Not(And(eric_eats_pizza, eric_eats_grilled_cheese)))
s.add(Or(arnold_eats_pizza, arnold_eats_grilled_cheese))
s.add(Not(And(arnold_eats_pizza, arnold_eats_grilled_cheese)))

# Different people in different houses
s.add(Not(And(eric_in_house_1, arnold_in_house_1)))
s.add(Not(And(eric_in_house_2, arnold_in_house_2)))

# Different people eating different foods
s.add(Not(And(eric_eats_pizza, arnold_eats_pizza)))
s.add(Not(And(eric_eats_grilled_cheese, arnold_eats_grilled_cheese)))

# Solve the constraints
if s.check() == sat:
    m = s.model()
    # Determine the assignments
    if m[eric_in_house_1]:
        eric_house = "1"
        arnold_house = "2"
    else:
        eric_house = "2"
        arnold_house = "1"

    if m[eric_eats_pizza]:
        eric_food = "pizza"
        arnold_food = "grilled cheese"
    else:
        eric_food = "grilled cheese"
        arnold_food = "pizza"

    solution = {
        "solution": {
            "header": ["House", "Name", "Food"],
            "rows": [
                [eric_house, "Eric", eric_food],
                [arnold_house, "Arnold", arnold_food]
            ]
        }
    }

    print(solution)
else:
    print("No solution found")