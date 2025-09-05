import json
from itertools import permutations

def solve_puzzle():
    # Houses are indexed 0-3 internally, corresponding to houses 1-4
    houses = [1, 2, 3, 4]
    names = ["Arnold", "Peter", "Eric", "Alice"]
    styles = ["victorian", "ranch", "colonial", "craftsman"]

    solutions = []

    # Constraints:
    # - Eric is in house 3 (index 2)
    # - Arnold is in house 4 (index 3)
    fixed_names = [None, None, "Eric", "Arnold"]
    remaining_names = [n for n in names if n not in {"Eric", "Arnold"}]  # Peter, Alice

    # Style constraints:
    # - Eric is in a Craftsman-style house -> house 3 (index 2) is craftsman
    fixed_styles = [None, None, "craftsman", None]
    remaining_styles = [s for s in styles if s != "craftsman"]  # victorian, ranch, colonial

    for perm_names in permutations(remaining_names):
        names_by_house = fixed_names[:]
        names_by_house[0], names_by_house[1] = perm_names

        for perm_styles in permutations(remaining_styles):
            styles_by_house = fixed_styles[:]
            styles_by_house[0], styles_by_house[1], styles_by_house[3] = perm_styles

            # Constraint 2: Ranch is directly left of Victorian
            try:
                ranch_idx = styles_by_house.index("ranch")
                victorian_idx = styles_by_house.index("victorian")
            except ValueError:
                continue
            if ranch_idx + 1 != victorian_idx:
                continue

            # Constraint 5: The person in the Victorian house is Alice
            alice_idx = names_by_house.index("Alice")
            if alice_idx != victorian_idx:
                continue

            # Constraint 1 already ensured by fixed_styles (Eric's house is craftsman)
            # Constraint 3 (Eric in third) and 4 (Arnold in fourth) enforced by fixed_names

            solutions.append((names_by_house, styles_by_house))

    if len(solutions) != 1:
        raise RuntimeError(f"Expected exactly one solution, found {len(solutions)}")

    names_by_house, styles_by_house = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": [
                [str(i + 1), names_by_house[i], styles_by_house[i]] for i in range(4)
            ],
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))