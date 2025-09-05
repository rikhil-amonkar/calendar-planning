import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Eric", "Arnold", "Alice", "Peter"]
    styles = ["craftsman", "colonial", "ranch", "victorian"]

    for name_perm in itertools.permutations(names):
        # Clue 1: Alice is in the second house.
        if name_perm[1] != "Alice":
            continue
        for style_perm in itertools.permutations(styles):
            # Clue 5: The person in a Craftsman-style house is Alice.
            try:
                craftsman_index = style_perm.index("craftsman")
            except ValueError:
                continue
            if name_perm[craftsman_index] != "Alice":
                continue

            # Clue 2: The person residing in a Victorian house is directly left of Peter.
            try:
                victorian_index = style_perm.index("victorian")
            except ValueError:
                continue
            if victorian_index == 3:  # Victorian house cannot be the rightmost.
                continue
            if name_perm[victorian_index + 1] != "Peter":
                continue

            # Clue 3: Peter is somewhere to the right of the person in a ranch-style home.
            try:
                ranch_index = style_perm.index("ranch")
            except ValueError:
                continue
            peter_index = name_perm.index("Peter")
            if peter_index <= ranch_index:
                continue

            # Clue 4: Arnold is somewhere to the right of the person in a Craftsman-style house.
            arnold_index = name_perm.index("Arnold")
            if arnold_index <= craftsman_index:
                continue

            # All constraints satisfied; construct the solution.
            rows = []
            for i in range(4):
                # Houses are numbered 1 to 4 (i+1 for human-friendly numbering)
                rows.append([str(i+1), name_perm[i], style_perm[i]])
            return {"solution": {"header": ["House", "Name", "HouseStyle"], "rows": rows}}

    return None

if __name__ == "__main__":
    solution = solve_puzzle()
    if solution is not None:
        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": None}))