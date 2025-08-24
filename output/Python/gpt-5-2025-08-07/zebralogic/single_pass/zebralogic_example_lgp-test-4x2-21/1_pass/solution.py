import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Eric", "Arnold", "Alice", "Peter"]
    styles = ["craftsman", "colonial", "ranch", "victorian"]

    solutions = []

    # Iterate over all possible assignments of names to houses
    for name_perm in permutations(names):
        # Clue 1: Alice is in the second house.
        if name_perm[1] != "Alice":
            continue

        pos_of_name = {name: idx + 1 for idx, name in enumerate(name_perm)}

        # Iterate over all possible assignments of house styles to houses
        for style_perm in permutations(styles):
            # Clue 5: The person in a Craftsman-style house is Alice.
            # Since Alice is in house 2, craftsman must be at house 2.
            if style_perm[1] != "craftsman":
                continue

            pos_of_style = {style: idx + 1 for idx, style in enumerate(style_perm)}

            # Clue 2: Victorian is directly left of Peter.
            if not (pos_of_style["victorian"] + 1 == pos_of_name["Peter"]):
                continue

            # Clue 3: Peter is somewhere to the right of the person in a ranch-style home.
            if not (pos_of_name["Peter"] > pos_of_style["ranch"]):
                continue

            # Clue 4: Arnold is somewhere to the right of the person in a Craftsman-style house.
            if not (pos_of_name["Arnold"] > pos_of_style["craftsman"]):
                continue

            solutions.append((name_perm, style_perm))

    if not solutions:
        raise ValueError("No solution found with given constraints.")

    # Assuming a unique solution; take the first
    name_perm, style_perm = solutions[0]

    # Build the output structure
    header = ["House", "Name", "HouseStyle"]
    rows = []
    for i, house in enumerate(houses):
        rows.append([str(house), name_perm[i], style_perm[i]])

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))