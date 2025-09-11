import itertools
import json

def solve_puzzle():
    # Define the lists of attributes
    names = ["Arnold", "Eric", "Alice", "Bob", "Peter"]
    vacations = ["mountain", "city", "cruise", "beach", "camping"]
    educations = ["doctorate", "high school", "bachelor", "associate", "master"]
    colors = ["blue", "red", "white", "yellow", "green"]
    phones = ["google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"]
    foods = ["grilled cheese", "stir fry", "pizza", "spaghetti", "stew"]

    # Generate all possible permutations for the attributes
    all_permutations = list(itertools.permutations(range(5)))

    # Function to check if a permutation satisfies all the clues
    def is_valid(name_order, vacation_order, education_order, color_order, phone_order, food_order):
        # Unpack the permutations into dictionaries for easier access
        name_dict = {name: i for i, name in enumerate(name_order)}
        vacation_dict = {vacation: i for i, vacation in enumerate(vacation_order)}
        education_dict = {education: i for i, education in enumerate(education_order)}
        color_dict = {color: i for i, color in enumerate(color_order)}
        phone_dict = {phone: i for i, phone in enumerate(phone_order)}
        food_dict = {food: i for i, food in enumerate(food_order)}

        # Check each clue
        if food_dict["stew"] == 0:
            return False
        if abs(food_dict["stir fry"] - education_dict["associate"]) != 2:
            return False
        if education_dict["bachelor"] != vacation_dict["mountain"]:
            return False
        if name_dict["Bob"] >= education_dict["doctorate"]:
            return False
        if phone_dict["samsung galaxy s21"] != 2:
            return False
        if name_dict["Eric"] != education_dict["doctorate"]:
            return False
        if education_dict["doctorate"] != 2:
            return False
        if food_dict["stir fry"] != education_dict["bachelor"]:
            return False
        if education_dict["doctorate"] != food_dict["pizza"]:
            return False
        if color_dict["green"] <= name_dict["Peter"]:
            return False
        if vacation_dict["camping"] != phone_dict["iphone 13"]:
            return False
        if name_dict["Alice"] != vacation_dict["cruise"]:
            return False
        if abs(education_dict["high school"] - phone_dict["samsung galaxy s21"]) != 1:
            return False
        if phone_dict["google pixel 6"] != name_dict["Arnold"]:
            return False
        if phone_dict["oneplus 9"] <= phone_dict["huawei p50"]:
            return False
        if name_dict["Arnold"] != food_dict["grilled cheese"]:
            return False
        if food_dict["grilled cheese"] == 3:
            return False
        if abs(education_dict["bachelor"] - color_dict["red"]) != 2:
            return False
        if vacation_dict["beach"] <= vacation_dict["city"]:
            return False
        if color_dict["green"] == 1:
            return False
        if color_dict["blue"] <= name_dict["Peter"]:
            return False
        if abs(vacation_dict["camping"] - color_dict["yellow"]) != 1:
            return False

        return True

    # Find the valid permutation
    for name_order in all_permutations:
        for vacation_order in all_permutations:
            for education_order in all_permutations:
                for color_order in all_permutations:
                    for phone_order in all_permutations:
                        for food_order in all_permutations:
                            if is_valid(name_order, vacation_order, education_order, color_order, phone_order, food_order):
                                break
                        else:
                            continue
                        break
                    else:
                        continue
                    break
                else:
                    continue
                break
            else:
                continue
            break

    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],
            "rows": []
        }
    }

    for house in range(5):
        solution["solution"]["rows"].append([
            str(house + 1),
            names[name_order[house]],
            vacations[vacation_order[house]],
            educations[education_order[house]],
            colors[color_order[house]],
            phones[phone_order[house]],
            foods[food_order[house]]
        ])

    return json.dumps(solution, indent=2)

# Output the solution
print(solve_puzzle())