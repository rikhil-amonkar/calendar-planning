import json
import itertools

def solve_puzzle():
    # Input variables (from the puzzle)
    houses = [1, 2]  # left to right
    names = ["Eric", "Arnold"]
    house_styles = ["victorian", "colonial"]

    solutions = []

    # Iterate over all possible assignments of names and house styles
    for name_perm in itertools.permutations(names, len(houses)):
        name_by_house = dict(zip(houses, name_perm))

        # Clue 2: Eric is in the first house.
        if name_by_house[1] != "Eric":
            continue

        for style_perm in itertools.permutations(house_styles, len(houses)):
            style_by_house = dict(zip(houses, style_perm))

            # Clue 1: Victorian is to the left of Colonial
            house_of_victorian = next(h for h in houses if style_by_house[h] == "victorian")
            house_of_colonial = next(h for h in houses if style_by_house[h] == "colonial")
            if not (house_of_victorian < house_of_colonial):
                continue

            # All constraints satisfied; record solution
            solutions.append((name_by_house, style_by_house))

    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")

    # Assuming a unique solution for this puzzle; take the first
    name_by_house, style_by_house = solutions[0]

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
    print(json.dumps(solution, ensure_ascii=False, indent=2))