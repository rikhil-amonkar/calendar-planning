import itertools
import json

def solve_puzzle():
    # Input variables
    houses = [1, 2]  # left to right
    names = ["Eric", "Arnold"]
    house_styles = ["victorian", "colonial"]

    # Helper to invert a mapping: value -> key
    def invert_map(m):
        return {v: k for k, v in m.items()}

    solutions = []

    # Enumerate all possible assignments ensuring uniqueness via permutations
    for name_perm in itertools.permutations(names, len(houses)):
        name_by_house = {house: name_perm[i] for i, house in enumerate(houses)}

        # Constraint: Eric is in the first house
        if name_by_house[1] != "Eric":
            continue

        for style_perm in itertools.permutations(house_styles, len(houses)):
            style_by_house = {house: style_perm[i] for i, house in enumerate(houses)}

            # Constraint: victorian is to the left of colonial
            style_pos = invert_map(style_by_house)
            if style_pos["victorian"] >= style_pos["colonial"]:
                continue

            # All constraints satisfied; record solution
            solutions.append((name_by_house, style_by_house))

    if len(solutions) != 1:
        raise ValueError(f"Expected exactly one solution, found {len(solutions)}.")

    name_by_house, style_by_house = solutions[0]

    # Build the required JSON structure
    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": []
        }
    }

    for h in sorted(houses):
        row = [str(h), name_by_house[h], style_by_house[h]]
        output["solution"]["rows"].append(row)

    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))