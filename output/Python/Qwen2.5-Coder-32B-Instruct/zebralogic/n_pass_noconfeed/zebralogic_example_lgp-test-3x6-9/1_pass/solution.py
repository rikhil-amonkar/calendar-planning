import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Peter", "Arnold", "Eric"]
    cars = ["toyota camry", "ford f150", "tesla model 3"]
    house_styles = ["ranch", "colonial", "victorian"]
    pets = ["cat", "dog", "fish"]
    occupations = ["engineer", "doctor", "teacher"]
    vacations = ["city", "mountain", "beach"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(cars)) * \
                       list(itertools.permutations(house_styles)) * \
                       list(itertools.permutations(pets)) * \
                       list(itertools.permutations(occupations)) * \
                       list(itertools.permutations(vacations))

    # Function to check if a given permutation satisfies all the clues
    def is_valid_solution(solution):
        (name_order, car_order, house_style_order, pet_order, occupation_order, vacation_order) = solution

        # Unpack the solution into house-specific details
        house1 = {"name": name_order[0], "car": car_order[0], "house_style": house_style_order[0],
                  "pet": pet_order[0], "occupation": occupation_order[0], "vacation": vacation_order[0]}
        house2 = {"name": name_order[1], "car": car_order[1], "house_style": house_style_order[1],
                  "pet": pet_order[1], "occupation": occupation_order[1], "vacation": vacation_order[1]}
        house3 = {"name": name_order[2], "car": car_order[2], "house_style": house_style_order[2],
                  "pet": pet_order[2], "occupation": occupation_order[2], "vacation": vacation_order[2]}

        # Check each clue
        if house1["pet"] != "fish":
            return False
        if house2["car"] != "toyota camry":
            return False
        if house2["vacation"] == "mountain" or house2["vacation"] == "city":
            return False
        if name_order.index("Peter") < house_style_order.index("ranch"):
            return False
        if house2["house_style"] != "colonial" or car_order.index("toyota camry") + 1 != house_style_order.index("colonial"):
            return False
        if house1["name"] != "Arnold" or house1["pet"] != "cat":
            return False
        if name_order.index("Eric") > vacation_order.index("mountain"):
            return False
        if name_order.index("engineer") == 2:
            return False
        if car_order.index("tesla model 3") > occupation_order.index("teacher"):
            return False
        if pet_order.index("dog") != occupation_order.index("engineer"):
            return False

        return True

    # Iterate over all permutations to find a valid solution
    for solution in all_permutations:
        if is_valid_solution(solution):
            (name_order, car_order, house_style_order, pet_order, occupation_order, vacation_order) = solution
            break

    # Prepare the result in the required JSON format
    result = {
        "solution": {
            "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
            "rows": [
                ["1", name_order[0], car_order[0], house_style_order[0], pet_order[0], occupation_order[0], vacation_order[0]],
                ["2", name_order[1], car_order[1], house_style_order[1], pet_order[1], occupation_order[1], vacation_order[1]],
                ["3", name_order[2], car_order[2], house_style_order[2], pet_order[2], occupation_order[2], vacation_order[2]]
            ]
        }
    }

    # Output the result as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    solve_puzzle()