import itertools
import json

def solve_puzzle():
    # Input variables
    houses = [1, 2, 3, 4]  # Left to right
    names = ["Eric", "Arnold", "Alice", "Peter"]
    styles = ["craftsman", "colonial", "ranch", "victorian"]

    # Constraints:
    # 1. Alice is in the second house.
    # 2. The person residing in a Victorian house is directly left of Peter.
    # 3. Peter is somewhere to the right of the person in a ranch-style home.
    # 4. Arnold is somewhere to the right of the person in a Craftsman-style house.
    # 5. The person in a Craftsman-style house is Alice.

    solutions = []

    # Permute names with Alice fixed at house 2
    other_names = [n for n in names if n != "Alice"]
    for perm_names in itertools.permutations(other_names):
        name_by_house = {}
        it = iter(perm_names)
        for h in houses:
            if h == 2:
                name_by_house[h] = "Alice"
            else:
                name_by_house[h] = next(it)

        # Early pruning based on constraints that don't depend on styles:
        # - Peter cannot be in house 1 (needs someone on the left to be Victorian).
        h_peter = next(h for h in houses if name_by_house[h] == "Peter")
        if h_peter == 1:
            continue
        # - Arnold must be to the right of the Craftsman (which is Alice in house 2, per constraint 5).
        h_arnold = next(h for h in houses if name_by_house[h] == "Arnold")
        if h_arnold <= 2:
            continue

        # Permute styles with Craftsman fixed at house 2 (since Craftsman is Alice)
        other_styles = [s for s in styles if s != "craftsman"]
        for perm_styles in itertools.permutations(other_styles):
            style_by_house = {}
            it_s = iter(perm_styles)
            for h in houses:
                if h == 2:
                    style_by_house[h] = "craftsman"
                else:
                    style_by_house[h] = next(it_s)

            # Check constraints:
            # 2. Victorian is directly left of Peter
            h_victorian = next(h for h in houses if style_by_house[h] == "victorian")
            if h_victorian + 1 != h_peter:
                continue

            # 3. Peter is to the right of Ranch
            h_ranch = next(h for h in houses if style_by_house[h] == "ranch")
            if not (h_peter > h_ranch):
                continue

            # 4. Arnold is to the right of Craftsman (house 2)
            h_craftsman = 2
            if not (h_arnold > h_craftsman):
                continue

            # 5. Craftsman is Alice (already enforced by fixing craftsman at house 2 and Alice at house 2)
            if name_by_house[h_craftsman] != "Alice":
                continue

            solutions.append((name_by_house, style_by_house))

    if not solutions:
        raise ValueError("No solution found.")
    if len(solutions) > 1:
        # If multiple solutions exist, choose consistent behavior (e.g., the first), but note ambiguity
        # For robustness, we still output the first solution found.
        pass

    name_by_house, style_by_house = solutions[0]

    # Build output JSON
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": [
                [str(h), name_by_house[h], style_by_house[h]] for h in houses
            ]
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))