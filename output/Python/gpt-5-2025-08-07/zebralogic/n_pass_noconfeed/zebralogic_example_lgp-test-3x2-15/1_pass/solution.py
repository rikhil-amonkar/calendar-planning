import itertools
import json

def solve_puzzle():
    # Input variables
    houses = [1, 2, 3]  # Left to right
    names = ["Arnold", "Peter", "Eric"]
    heights = ["short", "average", "very short"]

    solutions = []

    # Iterate over all possible assignments of names and heights to houses
    for name_perm in itertools.permutations(names):
        house_to_name = {house: name_perm[i] for i, house in enumerate(houses)}
        pos_name = {name: house for house, name in house_to_name.items()}

        # Constraint 1: Peter is somewhere to the right of Eric.
        if not (pos_name["Peter"] > pos_name["Eric"]):
            continue

        for height_perm in itertools.permutations(heights):
            house_to_height = {house: height_perm[i] for i, house in enumerate(houses)}
            pos_height = {height: house for house, height in house_to_height.items()}

            # Constraint 2: The person who is short is in the first house.
            if house_to_height[1] != "short":
                continue

            # Constraint 3: There is one house between short and very short.
            if abs(pos_height["short"] - pos_height["very short"]) != 2:
                continue

            # Constraint 4: Arnold and the person who is very short are next to each other.
            if abs(pos_name["Arnold"] - pos_height["very short"]) != 1:
                continue

            # All constraints satisfied, record solution
            solutions.append((house_to_name, house_to_height))

    # Expecting a unique solution
    if not solutions:
        raise ValueError("No solution found for the given puzzle.")
    # If multiple, select the first consistent solution (shouldn't happen with these clues)
    house_to_name, house_to_height = solutions[0]

    # Prepare output
    header = ["House", "Name", "Height"]
    rows = []
    for h in sorted(houses):
        rows.append([str(h), house_to_name[h], house_to_height[h]])

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))