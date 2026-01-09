import json
import itertools

def solve_puzzle():
    # Define domains
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    foods = ["pizza", "grilled cheese"]

    solutions = []

    # Enumerate all bijective assignments using only the standard library
    for name_perm in itertools.permutations(houses, len(names)):
        name_to_house = dict(zip(names, name_perm))

        # Clue 2: Arnold is not in the first house.
        if name_to_house["Arnold"] == 1:
            continue

        for food_perm in itertools.permutations(houses, len(foods)):
            food_to_house = dict(zip(foods, food_perm))

            # Clue 1: The person who is a pizza lover is in the second house.
            if food_to_house["pizza"] != 2:
                continue

            # If we reach here, constraints are satisfied
            solutions.append((name_to_house, food_to_house))

    if not solutions:
        raise RuntimeError("No solution found for the puzzle.")
    name_to_house, food_to_house = solutions[0]

    # Invert mappings to get attributes per house
    house_to_name = {h: n for n, h in name_to_house.items()}
    house_to_food = {h: f for f, h in food_to_house.items()}

    # Build JSON output
    rows = []
    for h in sorted(houses):
        rows.append([str(h), house_to_name[h], house_to_food[h]])

    result = {
        "solution": {
            "header": ["House", "Name", "Food"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))