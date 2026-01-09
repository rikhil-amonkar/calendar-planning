import json
from itertools import permutations, product

def solve_puzzle():
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    styles = ["victorian", "colonial"]

    # Generate all distinct assignments (AllDifferent) for names and styles
    name_assignments = []
    for perm in permutations(houses, len(names)):
        assign = dict(zip(names, perm))
        # Clue 2: Eric is in the first house
        if assign["Eric"] == 1:
            name_assignments.append(assign)

    style_assignments = []
    for perm in permutations(houses, len(styles)):
        assign = dict(zip(styles, perm))
        # Clue 1: Victorian is to the left of Colonial (i.e., lower house number)
        if assign["victorian"] < assign["colonial"]:
            style_assignments.append(assign)

    # Combine assignments; there are no cross-category constraints in this puzzle
    solutions = []
    for name_map, style_map in product(name_assignments, style_assignments):
        solutions.append((name_map, style_map))

    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")
    name_map, style_map = solutions[0]

    # Build rows ordered by house number
    rows = []
    for h in sorted(houses):
        name_at_house = next(n for n in names if name_map[n] == h)
        style_at_house = next(s for s in styles if style_map[s] == h)
        rows.append([str(h), name_at_house, style_at_house])

    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))