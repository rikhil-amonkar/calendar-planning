import json
from z3 import *

def main():
    solver = Solver()

    # Define variables for each house (1-5)
    names = [Int(f'name_{i+1}') for i in range(5)]
    hobbies = [Int(f'hobby_{i+1}') for i in range(5)]
    heights = [Int(f'height_{i+1}') for i in range(5)]
    foods = [Int(f'food_{i+1}') for i in range(5)]

    # Add constraints for distinct and ranges
    for var_list in [names, hobbies, heights, foods]:
        solver.add(Distinct(var_list))
        for var in var_list:
            solver.add(And(0 <= var, var <= 4))

    # Clue 1: Bob is photography enthusiast
    for i in range(5):
        solver.add(Implies(names[i] == 4, hobbies[i] == 4))

    # Clue 2: grilled cheese lover is tall
    for i in range(5):
        solver.add(Implies(foods[i] == 1, heights[i] == 1))

    # Clue 3: Peter not in house 2 (index 1)
    solver.add(names[1] != 1)

    # Clue 4: tall is directly left of stir fry (house 3 is tall, so house 4 has stir fry)
    solver.add(foods[3] == 2)  # house 4 (index 3) has stir fry

    # Clue 5: cooking lover has average height
    for i in range(5):
        solver.add(Implies(hobbies[i] == 1, heights[i] == 3))

    # Clue 6: Alice directly left of pizza lover
    solver.add(Or(
        And(names[0] == 3, foods[1] == 4),
        And(names[1] == 3, foods[2] == 4),
        And(names[2] == 3, foods[3] == 4),
        And(names[3] == 3, foods[4] == 4)
    ))

    # Clue 7: spaghetti eater not in house 2 (index 1)
    solver.add(foods[1] != 3)

    # Clue 8: Eric not in house 5 (index 4)
    solver.add(names[4] != 2)

    # Clue 9: Peter is short
    for i in range(5):
        solver.add(Implies(names[i] == 1, heights[i] == 4))

    # Clue 10: average height and gardening are adjacent
    adjacent_pairs = []
    for i in range(4):
        cond1 = And(heights[i] == 3, hobbies[i+1] == 3)
        cond2 = And(hobbies[i] == 3, heights[i+1] == 3)
        adjacent_pairs.append(Or(cond1, cond2))
    solver.add(Or(adjacent_pairs))

    # Clue 11: painting directly left of grilled cheese
    solver.add(Or(
        And(hobbies[0] == 0, foods[1] == 1),
        And(hobbies[1] == 0, foods[2] == 1),
        And(hobbies[2] == 0, foods[3] == 1),
        And(hobbies[3] == 0, foods[4] == 1)
    ))

    # Clue 12: very short in house 5 (index 4)
    solver.add(heights[4] == 2)

    # Clue 13: tall in house 3 (index 2)
    solver.add(heights[2] == 1)

    # Clue 14: Alice to the right of Bob
    bob_house = Sum([ If(names[i] == 4, i+1, 0) for i in range(5) ])
    alice_house = Sum([ If(names[i] == 3, i+1, 0) for i in range(5) ])
    solver.add(alice_house > bob_house)

    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()

        # Mapping lists
        name_list = ["Arnold", "Peter", "Eric", "Alice", "Bob"]
        hobby_list = ["painting", "cooking", "knitting", "gardening", "photography"]
        height_list = ["very tall", "tall", "very short", "average", "short"]
        food_list = ["stew", "grilled cheese", "stir fry", "spaghetti", "pizza"]

        # Prepare the rows
        rows = []
        for i in range(5):
            house_num = i + 1
            name_idx = model[names[i]].as_long()
            hobby_idx = model[hobbies[i]].as_long()
            height_idx = model[heights[i]].as_long()
            food_idx = model[foods[i]].as_long()

            row = [
                str(house_num),
                name_list[name_idx],
                hobby_list[hobby_idx],
                height_list[height_idx],
                food_list[food_idx]
            ]
            rows.append(row)

        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Height", "Food"],
                "rows": rows
            }
        }

        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()