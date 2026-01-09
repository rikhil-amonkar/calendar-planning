import json
from itertools import permutations

def solve_puzzle():
    # Define houses
    houses = [1, 2]

    # Define attributes
    names = ["Arnold", "Eric"]
    educations = ["associate", "high school"]
    heights = ["short", "very short"]
    foods = ["grilled cheese", "pizza"]
    drinks = ["tea", "water"]

    # Fixed food assignments from clues:
    # 2. The person who loves eating grilled cheese is in the second house.
    # => grilled cheese -> 2, pizza -> 1
    food_assignments = {
        "Food:grilled cheese": 2,
        "Food:pizza": 1
    }

    solutions = []

    # Try all permutations for other categories
    for name_perm in permutations(houses):
        assignments = dict(food_assignments)
        # Assign Names
        for i, v in enumerate(names):
            assignments[f"Name:{v}"] = name_perm[i]

        # 5. Arnold is the person who is a pizza lover.
        if assignments["Name:Arnold"] != assignments["Food:pizza"]:
            continue

        for edu_perm in permutations(houses):
            # Assign Educations
            for i, v in enumerate(educations):
                assignments[f"Education:{v}"] = edu_perm[i]

            # 3. The person with a high school diploma is the person who is a pizza lover.
            if assignments["Education:high school"] != assignments["Food:pizza"]:
                continue

            for height_perm in permutations(houses):
                # Assign Heights
                for i, v in enumerate(heights):
                    assignments[f"Height:{v}"] = height_perm[i]

                # 1. The person who is very short is the person who is a pizza lover.
                if assignments["Height:very short"] != assignments["Food:pizza"]:
                    continue

                for drink_perm in permutations(houses):
                    # Assign Drinks
                    for i, v in enumerate(drinks):
                        assignments[f"Drink:{v}"] = drink_perm[i]

                    # 4. The tea drinker is the person who loves eating grilled cheese.
                    if assignments["Drink:tea"] != assignments["Food:grilled cheese"]:
                        continue

                    # All constraints satisfied
                    solutions.append(assignments.copy())

    if not solutions:
        raise ValueError("No solution found for the given puzzle.")

    sol = solutions[0]

    # Helper to find which value in a category is at a given house
    def value_at_house(category, values, house):
        for v in values:
            if sol[f"{category}:{v}"] == house:
                return v
        return None

    rows = []
    for house in houses:
        row = [
            str(house),
            value_at_house("Name", names, house),
            value_at_house("Education", educations, house),
            value_at_house("Height", heights, house),
            value_at_house("Food", foods, house),
            value_at_house("Drink", drinks, house),
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))