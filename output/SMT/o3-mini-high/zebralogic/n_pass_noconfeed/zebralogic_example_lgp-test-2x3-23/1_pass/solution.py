import json
from z3 import *

def solve_puzzle():
    solver = Solver()

    # Create variables for each house: house1 and house2.
    house1_name = Int('house1_name')
    house1_child = Int('house1_child')
    house1_food = Int('house1_food')

    house2_name = Int('house2_name')
    house2_child = Int('house2_child')
    house2_food = Int('house2_food')

    # Domain constraints: each variable takes a value in {0,1}
    # For Name: 0 -> Eric, 1 -> Arnold
    # For Children: 0 -> Bella, 1 -> Fred
    # For Food: 0 -> grilled cheese, 1 -> pizza
    solver.add(And(house1_name >= 0, house1_name <= 1))
    solver.add(And(house1_child >= 0, house1_child <= 1))
    solver.add(And(house1_food >= 0, house1_food <= 1))

    solver.add(And(house2_name >= 0, house2_name <= 1))
    solver.add(And(house2_child >= 0, house2_child <= 1))
    solver.add(And(house2_food >= 0, house2_food <= 1))

    # All houses must have distinct attributes.
    solver.add(Distinct(house1_name, house2_name))
    solver.add(Distinct(house1_child, house2_child))
    solver.add(Distinct(house1_food, house2_food))

    # Clue 1: The person who is a pizza lover is Arnold.
    # Pizza is represented by 1 and Arnold is represented by 1.
    solver.add(Implies(house1_food == 1, house1_name == 1))
    solver.add(Implies(house2_food == 1, house2_name == 1))

    # Clue 2: The person who loves eating grilled cheese is directly left of the person whose child is named Fred.
    # With 2 houses, this forces house1's food to be grilled cheese (0)
    # and house2's child to be Fred (1).
    solver.add(house1_food == 0)
    solver.add(house2_child == 1)

    if solver.check() == sat:
        model = solver.model()

        namesMapping = {0: "Eric", 1: "Arnold"}
        childrenMapping = {0: "Bella", 1: "Fred"}
        foodMapping = {0: "grilled cheese", 1: "pizza"}

        house1 = [
            "1",
            namesMapping[model[house1_name].as_long()],
            childrenMapping[model[house1_child].as_long()],
            foodMapping[model[house1_food].as_long()]
        ]
        house2 = [
            "2",
            namesMapping[model[house2_name].as_long()],
            childrenMapping[model[house2_child].as_long()],
            foodMapping[model[house2_food].as_long()]
        ]

        solution = {
            "solution": {
                "header": ["House", "Name", "Children", "Food"],
                "rows": [house1, house2]
            }
        }
        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    solve_puzzle()