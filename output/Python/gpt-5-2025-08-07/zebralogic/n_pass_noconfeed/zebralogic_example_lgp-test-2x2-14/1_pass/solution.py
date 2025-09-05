import itertools
import json

def solve():
    # Define puzzle parameters
    houses = [1, 2]  # House numbers from left (1) to right (2)
    names = ["Eric", "Arnold"]
    foods = ["pizza", "grilled cheese"]

    # Generate all possible bijective assignments (permutations) for each attribute
    name_permutations = list(itertools.permutations(names))
    food_permutations = list(itertools.permutations(foods))

    solutions = []

    for name_assign in name_permutations:
        # Clue 2: Arnold is not in the first house.
        if name_assign[0] == "Arnold":
            continue

        for food_assign in food_permutations:
            # Clue 1: The person who is a pizza lover is in the second house.
            if food_assign[1] != "pizza":
                continue

            # If all constraints are satisfied, record this solution
            solutions.append((name_assign, food_assign))

    if not solutions:
        raise ValueError("No solution found for the given constraints.")

    # Assuming a unique solution as per standard Zebra puzzles
    name_assign, food_assign = solutions[0]

    # Prepare output in required JSON structure
    output = {
        "solution": {
            "header": ["House", "Name", "Food"],
            "rows": []
        }
    }

    # Maintain the exact order of houses (1, 2)
    for i, house in enumerate(houses):
        row = [str(house), name_assign[i], food_assign[i]]
        output["solution"]["rows"].append(row)

    return output

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, ensure_ascii=False, indent=2))