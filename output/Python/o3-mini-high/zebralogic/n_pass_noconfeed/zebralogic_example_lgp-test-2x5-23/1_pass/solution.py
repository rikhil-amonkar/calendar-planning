import itertools
import json

def is_valid_solution(houses):
    # Clue 1: The person who is very short is the person who is a pizza lover.
    for house in houses:
        if house["Height"] == "very short":
            if house["Food"] != "pizza":
                return False
        if house["Food"] == "pizza":
            if house["Height"] != "very short":
                return False

    # Clue 2: The person who loves eating grilled cheese is in the second house.
    for house in houses:
        if house["Food"] == "grilled cheese":
            if house["House"] != "2":
                return False

    # Clue 3: The person with a high school diploma is the person who is a pizza lover.
    for house in houses:
        if house["Education"] == "high school":
            if house["Food"] != "pizza":
                return False
        if house["Food"] == "pizza":
            if house["Education"] != "high school":
                return False

    # Clue 4: The tea drinker is the person who loves eating grilled cheese.
    for house in houses:
        if house["Drink"] == "tea":
            if house["Food"] != "grilled cheese":
                return False
        if house["Food"] == "grilled cheese":
            if house["Drink"] != "tea":
                return False

    # Clue 5: Arnold is the person who is a pizza lover.
    for house in houses:
        if house["Name"] == "Arnold":
            if house["Food"] != "pizza":
                return False

    return True

def solve_puzzle():
    names = ["Arnold", "Eric"]
    educations = ["associate", "high school"]
    heights = ["short", "very short"]
    foods = ["grilled cheese", "pizza"]
    drinks = ["tea", "water"]
    houses_numbers = ["1", "2"]

    # Iterate over all permutations for each attribute and check constraints
    for names_perm in itertools.permutations(names):
        for educations_perm in itertools.permutations(educations):
            for heights_perm in itertools.permutations(heights):
                for foods_perm in itertools.permutations(foods):
                    for drinks_perm in itertools.permutations(drinks):
                        houses = []
                        for i, house in enumerate(houses_numbers):
                            houses.append({
                                "House": house,
                                "Name": names_perm[i],
                                "Education": educations_perm[i],
                                "Height": heights_perm[i],
                                "Food": foods_perm[i],
                                "Drink": drinks_perm[i]
                            })
                        if is_valid_solution(houses):
                            return houses
    return None

def main():
    solution = solve_puzzle()
    if solution is None:
        output = {
            "solution": {
                "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
                "rows": []
            }
        }
    else:
        # Order the houses by their number (already in order: "1", "2")
        rows = []
        for house in solution:
            rows.append([
                house["House"],
                house["Name"],
                house["Education"],
                house["Height"],
                house["Food"],
                house["Drink"]
            ])
        output = {
            "solution": {
                "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
                "rows": rows
            }
        }
    print(json.dumps(output))

if __name__ == "__main__":
    main()