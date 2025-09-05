import itertools
import json

def solve_puzzle():
    # Input variables (puzzle parameters)
    houses = [1, 2, 3, 4]
    names = ["Peter", "Arnold", "Alice", "Eric"]
    colors = ["yellow", "green", "red", "white"]

    solutions = []

    # Iterate over all possible assignments of names to houses
    for name_perm in itertools.permutations(names):
        name_at = {houses[i]: name_perm[i] for i in range(4)}
        pos_name = {name_perm[i]: houses[i] for i in range(4)}

        # Constraint 2: Peter is in the first house.
        if name_at[1] != "Peter":
            continue

        # Constraint 4: Arnold is directly left of Eric.
        if pos_name["Arnold"] + 1 != pos_name["Eric"]:
            continue

        # Iterate over all possible assignments of colors to houses
        for color_perm in itertools.permutations(colors):
            color_at = {houses[i]: color_perm[i] for i in range(4)}
            pos_color = {color_perm[i]: houses[i] for i in range(4)}

            # Constraint 1: The person whose favorite color is green is in the third house.
            if color_at[3] != "green":
                continue

            # Constraint 5: Eric is the person who loves yellow.
            if color_at[pos_name["Eric"]] != "yellow":
                continue

            # Constraint 3: There is one house between red and yellow.
            if abs(pos_color["red"] - pos_color["yellow"]) != 2:
                continue

            # All constraints satisfied; record solution
            row_data = [[str(h), name_at[h], color_at[h]] for h in houses]
            solutions.append(row_data)

    # Prepare JSON output
    result = {
        "solution": {
            "header": ["House", "Name", "Color"],
            "rows": solutions[0] if solutions else []
        }
    }
    return json.dumps(result, ensure_ascii=False)

if __name__ == "__main__":
    print(solve_puzzle())