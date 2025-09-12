from z3 import *

def solve_puzzle():
    # Create a solver instance
    solver = Solver()

    # Define domains
    houses = [1, 2, 3, 4, 5]
    names = ["Arnold", "Peter", "Eric", "Alice", "Bob"]
    hobbies = ["painting", "cooking", "knitting", "gardening", "photography"]
    heights = ["very tall", "tall", "very short", "average", "short"]
    foods = ["stew", "grilled cheese", "stir fry", "spaghetti", "pizza"]

    # Create variables
    name_vars = {h: Int(f"name_{h}") for h in houses}
    hobby_vars = {h: Int(f"hobby_{h}") for h in houses}
    height_vars = {h: Int(f"height_{h}") for h in houses}
    food_vars = {h: Int(f"food_{h}") for h in houses}

    # Add domain constraints
    for h in houses:
        solver.add(name_vars[h] >= 0, name_vars[h] < len(names))
        solver.add(hobby_vars[h] >= 0, hobby_vars[h] < len(hobbies))
        solver.add(height_vars[h] >= 0, height_vars[h] < len(heights))
        solver.add(food_vars[h] >= 0, food_vars[h] < len(foods))

    # All values must be unique
    solver.add(Distinct([name_vars[h] for h in houses]))
    solver.add(Distinct([hobby_vars[h] for h in houses]))
    solver.add(Distinct([height_vars[h] for h in houses]))
    solver.add(Distinct([food_vars[h] for h in houses]))

    # Clue 1: Bob is the photography enthusiast.
    solver.add(name_vars[houses[0]] != names.index("Bob") | hobby_vars[houses[0]] == hobbies.index("photography"))
    solver.add(name_vars[houses[1]] != names.index("Bob") | hobby_vars[houses[1]] == hobbies.index("photography"))
    solver.add(name_vars[houses[2]] != names.index("Bob") | hobby_vars[houses[2]] == hobbies.index("photography"))
    solver.add(name_vars[houses[3]] != names.index("Bob") | hobby_vars[houses[3]] == hobbies.index("photography"))
    solver.add(name_vars[houses[4]] != names.index("Bob") | hobby_vars[houses[4]] == hobbies.index("photography"))

    # Clue 2: The person who loves eating grilled cheese is the person who is tall.
    for h in houses:
        solver.add(Implies(food_vars[h] == foods.index("grilled cheese"), height_vars[h] == heights.index("tall")))

    # Clue 3: Peter is not in the second house.
    solver.add(name_vars[2] != names.index("Peter"))

    # Clue 4: The person who is tall is directly left of the person who loves stir fry.
    solver.add(Implies(height_vars[1] == heights.index("tall"), food_vars[2] == foods.index("stir fry")))
    solver.add(Implies(height_vars[2] == heights.index("tall"), food_vars[3] == foods.index("stir fry")))
    solver.add(Implies(height_vars[3] == heights.index("tall"), food_vars[4] == foods.index("stir fry")))

    # Clue 5: The person who loves cooking is the person who has an average height.
    for h in houses:
        solver.add(Implies(food_vars[h] == foods.index("cooking"), height_vars[h] == heights.index("average")))

    # Clue 6: Alice is directly left of the person who is a pizza lover.
    solver.add(Implies(name_vars[1] == names.index("Alice"), food_vars[2] == foods.index("pizza")))
    solver.add(Implies(name_vars[2] == names.index("Alice"), food_vars[3] == foods.index("pizza")))
    solver.add(Implies(name_vars[3] == names.index("Alice"), food_vars[4] == foods.index("pizza")))

    # Clue 7: The person who loves the spaghetti eater is not in the second house.
    solver.add(food_vars[2] != foods.index("spaghetti"))

    # Clue 8: Eric is not in the fifth house.
    solver.add(name_vars[5] != names.index("Eric"))

    # Clue 9: The person who is short is Peter.
    for h in houses:
        solver.add(Implies(name_vars[h] == names.index("Peter"), height_vars[h] == heights.index("short")))

    # Clue 10: The person who has an average height and the person who enjoys gardening are next to each other.
    solver.add(Or(
        And(height_vars[1] == heights.index("average"), hobby_vars[2] == hobbies.index("gardening")),
        And(height_vars[2] == heights.index("average"), hobby_vars[1] == hobbies.index("gardening")),
        And(height_vars[2] == heights.index("average"), hobby_vars[3] == hobbies.index("gardening")),
        And(height_vars[3] == heights.index("average"), hobby_vars[2] == hobbies.index("gardening")),
        And(height_vars[3] == heights.index("average"), hobby_vars[4] == hobbies.index("gardening")),
        And(height_vars[4] == heights.index("average"), hobby_vars[3] == hobbies.index("gardening")),
        And(height_vars[4] == heights.index("average"), hobby_vars[5] == hobbies.index("gardening")),
        And(height_vars[5] == heights.index("average"), hobby_vars[4] == hobbies.index("gardening"))
    ))

    # Clue 11: The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
    solver.add(Implies(hobby_vars[1] == hobbies.index("painting"), food_vars[2] == foods.index("grilled cheese")))
    solver.add(Implies(hobby_vars[2] == hobbies.index("painting"), food_vars[3] == foods.index("grilled cheese")))
    solver.add(Implies(hobby_vars[3] == hobbies.index("painting"), food_vars[4] == foods.index("grilled cheese")))
    solver.add(Implies(hobby_vars[4] == hobbies.index("painting"), food_vars[5] == foods.index("grilled cheese")))

    # Clue 12: The person who is very short is in the fifth house.
    solver.add(height_vars[5] == heights.index("very short"))

    # Clue 13: The person who is tall is in the third house.
    solver.add(height_vars[3] == heights.index("tall"))

    # Clue 14: Alice is somewhere to the right of the photography enthusiast.
    solver.add(Or(
        And(hobby_vars[1] == hobbies.index("photography"), name_vars[2] == names.index("Alice")),
        And(hobby_vars[1] == hobbies.index("photography"), name_vars[3] == names.index("Alice")),
        And(hobby_vars[1] == hobbies.index("photography"), name_vars[4] == names.index("Alice")),
        And(hobby_vars[1] == hobbies.index("photography"), name_vars[5] == names.index("Alice")),
        And(hobby_vars[2] == hobbies.index("photography"), name_vars[3] == names.index("Alice")),
        And(hobby_vars[2] == hobbies.index("photography"), name_vars[4] == names.index("Alice")),
        And(hobby_vars[2] == hobbies.index("photography"), name_vars[5] == names.index("Alice")),
        And(hobby_vars[3] == hobbies.index("photography"), name_vars[4] == names.index("Alice")),
        And(hobby_vars[3] == hobbies.index("photography"), name_vars[5] == names.index("Alice")),
        And(hobby_vars[4] == hobbies.index("photography"), name_vars[5] == names.index("Alice"))
    ))

    # Check if the problem is solvable
    if solver.check() == sat:
        model = solver.model()
        result = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Height", "Food"],
                "rows": []
            }
        }
        for h in houses:
            name = names[model.evaluate(name_vars[h]).as_long()]
            hobby = hobbies[model.evaluate(hobby_vars[h]).as_long()]
            height = heights[model.evaluate(height_vars[h]).as_long()]
            food = foods[model.evaluate(food_vars[h]).as_long()]
            result["solution"]["rows"].append([str(h), name, hobby, height, food])
        return result
    else:
        return None

import json
print(json.dumps(solve_puzzle(), indent=2))