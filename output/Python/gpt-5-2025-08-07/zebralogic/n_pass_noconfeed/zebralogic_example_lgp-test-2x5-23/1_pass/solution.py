import json
from itertools import permutations

def solve_puzzle():
    # Define houses and attributes
    houses = [1, 2]
    names = ["Arnold", "Eric"]
    educations = ["associate", "high school"]
    heights = ["short", "very short"]
    foods = ["grilled cheese", "pizza"]
    drinks = ["tea", "water"]

    solutions = []

    # Try all permutations while enforcing constraints
    for name_perm in permutations(names):
        for edu_perm in permutations(educations):
            for height_perm in permutations(heights):
                for food_perm in permutations(foods):
                    # Clue 2: The person who loves eating grilled cheese is in the second house.
                    if food_perm[1] != "grilled cheese":
                        continue

                    # Clue 1: The person who is very short is the person who is a pizza lover.
                    idx_very_short = height_perm.index("very short")
                    if food_perm[idx_very_short] != "pizza":
                        continue

                    # Clue 3: The person with a high school diploma is the person who is a pizza lover.
                    idx_high_school = edu_perm.index("high school")
                    if food_perm[idx_high_school] != "pizza":
                        continue

                    # Clue 5: Arnold is the person who is a pizza lover.
                    idx_arnold = name_perm.index("Arnold")
                    if food_perm[idx_arnold] != "pizza":
                        continue

                    for drink_perm in permutations(drinks):
                        # Clue 4: The tea drinker is the person who loves eating grilled cheese.
                        idx_tea = drink_perm.index("tea")
                        if food_perm[idx_tea] != "grilled cheese":
                            continue

                        # Assemble solution rows for each house
                        rows = []
                        for i, house in enumerate(houses):
                            rows.append([
                                str(house),
                                name_perm[i],
                                edu_perm[i],
                                height_perm[i],
                                food_perm[i],
                                drink_perm[i],
                            ])
                        solutions.append(rows)

    if not solutions:
        raise ValueError("No solution found for the given puzzle.")

    # Assuming a unique solution, take the first one
    result = {
        "solution": {
            "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
            "rows": solutions[0]
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))