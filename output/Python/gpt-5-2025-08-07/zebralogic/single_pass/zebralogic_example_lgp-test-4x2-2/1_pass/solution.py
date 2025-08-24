import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Arnold", "Peter", "Eric", "Alice"]
    styles = ["victorian", "ranch", "colonial", "craftsman"]

    solutions = []

    for name_perm in itertools.permutations(names):
        # Clue 3: Eric is in the third house.
        if name_perm[2] != "Eric":
            continue
        # Clue 4: Arnold is in the fourth house.
        if name_perm[3] != "Arnold":
            continue

        for style_perm in itertools.permutations(styles):
            # Clue 2: The ranch is directly left of the Victorian.
            idx_ranch = style_perm.index("ranch")
            idx_vict = style_perm.index("victorian")
            if idx_ranch + 1 != idx_vict:
                continue

            valid = True
            for i in range(4):
                name_i = name_perm[i]
                style_i = style_perm[i]

                # Clue 1: Eric is the person in a Craftsman-style house.
                if name_i == "Eric" and style_i != "craftsman":
                    valid = False
                    break
                if style_i == "craftsman" and name_i != "Eric":
                    valid = False
                    break

                # Clue 5: The person residing in a Victorian house is Alice.
                if style_i == "victorian" and name_i != "Alice":
                    valid = False
                    break
                if name_i == "Alice" and style_i != "victorian":
                    valid = False
                    break

            if valid:
                solutions.append((name_perm, style_perm))

    if not solutions:
        raise ValueError("No solution found based on the provided constraints.")

    # Expecting a unique solution; take the first
    name_perm, style_perm = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": [
                [str(h), name_perm[h - 1], style_perm[h - 1]] for h in houses
            ],
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))