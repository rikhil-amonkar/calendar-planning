import itertools
import json

def solve_puzzle():
    # Puzzle setup
    houses = [1, 2, 3]  # left to right
    names = ["Arnold", "Peter", "Eric"]
    heights = ["short", "average", "very short"]

    solutions = []

    # Iterate over all possible assignments
    for name_perm in itertools.permutations(names):
        # Mapping: house -> name and name -> house
        house_to_name = {house: name_perm[house - 1] for house in houses}
        name_to_house = {name_perm[i]: i + 1 for i in range(3)}

        for height_perm in itertools.permutations(heights):
            # Mapping: house -> height and height -> house
            house_to_height = {house: height_perm[house - 1] for house in houses}
            height_to_house = {height_perm[i]: i + 1 for i in range(3)}

            # Apply constraints:

            # 2. The person who is short is in the first house.
            if house_to_height[1] != "short":
                continue

            # 3. There is one house between the person who is short and the person who is very short.
            if abs(height_to_house["short"] - height_to_house["very short"]) != 2:
                continue

            # 4. Arnold and the person who is very short are next to each other.
            if abs(name_to_house["Arnold"] - height_to_house["very short"]) != 1:
                continue

            # 1. Peter is somewhere to the right of Eric.
            if not (name_to_house["Peter"] > name_to_house["Eric"]):
                continue

            # If all constraints passed, record the solution
            solutions.append((house_to_name, house_to_height))

    if not solutions:
        raise RuntimeError("No solution found with the given constraints.")
    if len(solutions) > 1:
        # In case multiple solutions are found, we still output the first but this flags ambiguity.
        pass

    house_to_name, house_to_height = solutions[0]

    # Build the required JSON structure
    result = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": [
                [str(h), house_to_name[h], house_to_height[h]] for h in houses
            ],
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))