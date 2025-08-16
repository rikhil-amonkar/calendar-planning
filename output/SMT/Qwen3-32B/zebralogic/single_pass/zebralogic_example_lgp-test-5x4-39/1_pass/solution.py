from z3 import *

def solve_puzzle():
    solver = Solver()

    # Variables for each house (0-4)
    names = [Int(f"name_{i}") for i in range(5)]
    hobbies = [Int(f"hobby_{i}") for i in range(5)]
    heights = [Int(f"height_{i}") for i in range(5)]
    foods = [Int(f"food_{i}") for i in range(5)]

    # Add constraints for distinct and ranges
    for lst in [names, hobbies, heights, foods]:
        for var in lst:
            solver.add(And(0 <= var, var <= 4))
        solver.add(Distinct(lst))

    # Clue 1: Bob (name 4) has hobby photography (4)
    for i in range(5):
        solver.add(Implies(names[i] == 4, hobbies[i] == 4))

    # Clue 2: grilled cheese (1) → tall (1)
    for i in range(5):
        solver.add(Implies(foods[i] == 1, heights[i] == 1))

    # Clue 3: Peter (1) not in house 2 (index 1)
    solver.add(names[1] != 1)

    # Clue 4: tall (1) is in house 3 (index 2)
    solver.add(heights[2] == 1)
    # stir fry (2) is in house 4 (index 3)
    solver.add(foods[3] == 2)

    # Clue 5: cooking (1) → average (3)
    for i in range(5):
        solver.add(Implies(hobbies[i] == 1, heights[i] == 3))

    # Clue 6: Alice (3) directly left of pizza (4)
    for i in range(4):  # i can be 0-3
        solver.add(Implies(names[i] == 3, foods[i+1] == 4))

    # Clue 7: spaghetti (3) not in house 2 (index 1)
    solver.add(foods[1] != 3)

    # Clue 8: Eric (2) not in house 5 (index 4)
    solver.add(names[4] != 2)

    # Clue 9: Peter (1) → short (4)
    for i in range(5):
        solver.add(Implies(names[i] == 1, heights[i] == 4))

    # Clue 10: average (3) and gardening (3) adjacent
    clue10 = Or([Or(And(heights[i] == 3, hobbies[i+1] == 3), And(hobbies[i] == 3, heights[i+1] == 3)) for i in range(4)])
    solver.add(clue10)

    # Clue 11: painting (0) directly left of grilled cheese (1)
    for i in range(4):
        solver.add(Implies(hobbies[i] == 0, foods[i+1] == 1))

    # Clue 12: very short (2) in house 5 (index 4)
    solver.add(heights[4] == 2)

    # Clue 14: Alice (3) to the right of Bob (4)
    for i in range(5):
        for j in range(5):
            solver.add(Implies(And(names[i] == 4, names[j] == 3), j > i))

    if solver.check() == sat:
        model = solver.model()

        # Mappings
        name_map = {0: "Arnold", 1: "Peter", 2: "Eric", 3: "Alice", 4: "Bob"}
        hobby_map = {0: "painting", 1: "cooking", 2: "knitting", 3: "gardening", 4: "photography"}
        height_map = {0: "very tall", 1: "tall", 2: "very short", 3: "average", 4: "short"}
        food_map = {0: "stew", 1: "grilled cheese", 2: "stir fry", 3: "spaghetti", 4: "pizza"}

        rows = []
        for i in range(5):
            house_num = i + 1
            name = name_map[model.evaluate(names[i]).as_long()]
            hobby = hobby_map[model.evaluate(hobbies[i]).as_long()]
            height = height_map[model.evaluate(heights[i]).as_long()]
            food = food_map[model.evaluate(foods[i]).as_long()]
            rows.append([str(house_num), name, hobby, height, food])

        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Height", "Food"],
                "rows": rows
            }
        }

        return solution
    else:
        return {"solution": None}

# Call the function and print the JSON
solution = solve_puzzle()
import json
print(json.dumps(solution, indent=2))