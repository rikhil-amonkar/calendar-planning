import json
from z3 import *

def main():
    # Define the possible values for each category as lists
    names_list = ["Arnold", "Peter", "Eric", "Alice"]
    styles_list = ["craftsman", "colonial", "victorian", "ranch"]
    hair_list = ["red", "blonde", "black", "brown"]
    children_list = ["Bella", "Fred", "Meredith", "Samantha"]
    book_list = ["mystery", "fantasy", "romance", "science fiction"]

    # Create Z3 variables for each house (1-4) and each attribute
    # Houses are 1-4, but indexes 0-3 in the lists
    name = [Int(f'name_{i+1}') for i in range(4)]
    style = [Int(f'style_{i+1}') for i in range(4)]
    hair = [Int(f'hair_{i+1}') for i in range(4)]
    child = [Int(f'child_{i+1}') for i in range(4)]
    book = [Int(f'book_{i+1}') for i in range(4)]

    solver = Solver()

    # Add constraints that each attribute is a permutation (all different and 0-3)
    for attr in [name, style, hair, child, book]:
        for var in attr:
            solver.add(And(0 <= var, var <= 3))
        solver.add(Distinct(attr))

    # Add specific constraints from the clues
    # Clue 1: Craftsman in house 3 (index 2)
    solver.add(style[2] == 0)  # craftsman is 0

    # Clue 3: house 4 (index 3) has brown hair (3)
    solver.add(hair[3] == 3)

    # Clue 4: house 4 (index 3) has child Samantha (3)
    solver.add(child[3] == 3)

    # Clue 9: house 2 (index 1) has black hair (2)
    solver.add(hair[1] == 2)

    # Clue 12: Eric is in house 2 (index 1)
    solver.add(name[1] == 2)  # Eric is 2

    # Clue 5: ranch (style 3) is to the right of red hair (hair 0)
    red_house = Sum([If(hair[i] == 0, (i+1), 0) for i in range(4)])
    ranch_house = Sum([If(style[i] == 3, (i+1), 0) for i in range(4)])
    solver.add(ranch_house > red_house)

    # Clue 2: Alice (3) has book romance (2)
    for i in range(4):
        solver.add(Implies(name[i] == 3, book[i] == 2))

    # Clue 6: Peter (1) has child Bella (0)
    for i in range(4):
        solver.add(Implies(name[i] == 1, child[i] == 0))

    # Clue 7: Arnold (0) has hair red (0)
    for i in range(4):
        solver.add(Implies(name[i] == 0, hair[i] == 0))

    # Clue 8: Alice (3) has style colonial (1)
    for i in range(4):
        solver.add(Implies(name[i] == 3, style[i] == 1))

    # Clue 10: Peter (1) has book fantasy (1)
    for i in range(4):
        solver.add(Implies(name[i] == 1, book[i] == 1))

    # Clue 11: Arnold (0) has child Meredith (2)
    for i in range(4):
        solver.add(Implies(name[i] == 0, child[i] == 2))

    # Clue 13: Arnold (0) has book science fiction (3)
    for i in range(4):
        solver.add(Implies(name[i] == 0, book[i] == 3))

    # Clue 12: Eric (2) has hair black (2)
    for i in range(4):
        solver.add(Implies(name[i] == 2, hair[i] == 2))

    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()

        # Extract the solution for each house
        solution_rows = []
        for i in range(4):
            house_num = i + 1
            name_val = model[name[i]].as_long()
            style_val = model[style[i]].as_long()
            hair_val = model[hair[i]].as_long()
            child_val = model[child[i]].as_long()
            book_val = model[book[i]].as_long()

            # Convert to strings
            solution_row = [
                str(house_num),
                names_list[name_val],
                styles_list[style_val],
                hair_list[hair_val],
                children_list[child_val],
                book_list[book_val]
            ]
            solution_rows.append(solution_row)

        # Prepare the JSON output
        output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
                "rows": solution_rows
            }
        }

        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()