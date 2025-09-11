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
        # Create dictionaries to map indices to attribute values
        name_dict = {i: name_order[i] for i in range(5)}
        vacation_dict = {i: vacation_order[i] for i in range(5)}
        education_dict = {i: education_order[i] for i in range(5)}
        color_dict = {i: color_order[i] for i in range(5)}
        phone_dict = {i: phone_order[i] for i in range(5)}
        food_dict = {i: food_order[i] for i in range(5)}

        # Reverse dictionaries to map attribute values to indices
        name_value_dict = {name_order[i]: i for i in range(5)}
        vacation_value_dict = {vacation_order[i]: i for i in range(5)}
        education_value_dict = {education_order[i]: i for i in range(5)}
        color_value_dict = {color_order[i]: i for i in range(5)}
        phone_value_dict = {phone_order[i]: i for i in range(5)}
        food_value_dict = {foods[i]: food_order[i] for i in range(5)}

        # Check each clue using the reverse dictionaries
        if food_value_dict.get("stew") == 0:
            return False
        if abs(food_value_dict.get("stir fry", -1) - education_value_dict.get("associate", -1)) != 2:
            return False
        if education_value_dict.get("bachelor", -1) != vacation_value_dict.get("mountain", -1):
            return False
        if name_value_dict.get("Bob", -1) >= education_value_dict.get("doctorate", -1):
            return False
        if phone_value_dict.get("samsung galaxy s21", -1) != 2:
            return False
        if name_value_dict.get("Eric", -1) != education_value_dict.get("doctorate", -1):
            return False
        if education_value_dict.get("doctorate", -1) != 2:
            return False
        if food_value_dict.get("stir fry", -1) != education_value_dict.get("bachelor", -1):
            return False
        if education_value_dict.get("doctorate", -1) != food_value_dict.get("pizza", -1):
            return False
        if color_value_dict.get("green", -1) <= name_value_dict.get("Peter", -1):
            return False
        if vacation_value_dict.get("camping", -1) != phone_value_dict.get("iphone 13", -1):
            return False
        if name_value_dict.get("Alice", -1) != vacation_value_dict.get("cruise", -1):
            return False
        if abs(education_value_dict.get("high school", -1) - phone_value_dict.get("samsung galaxy s21", -1)) != 1:
            return False
        if phone_value_dict.get("google pixel 6", -1) != name_value_dict.get("Arnold", -1):
            return False
        if phone_value_dict.get("oneplus 9", -1) <= phone_value_dict.get("huawei p50", -1):
            return False
        if name_value_dict.get("Arnold", -1) != food_value_dict.get("grilled cheese", -1):
            return False
        if food_value_dict.get("grilled cheese", -1) == 3:
            return False
        if abs(education_value_dict.get("bachelor", -1) - color_value_dict.get("red", -1)) != 2:
            return False
        if vacation_value_dict.get("beach", -1) <= vacation_value_dict.get("city", -1):
            return False
        if color_value_dict.get("green", -1) == 1:
            return False
        if color_value_dict.get("blue", -1) <= name_value_dict.get("Peter", -1):
            return False
        if abs(vacation_value_dict.get("camping", -1) - color_value_dict.get("yellow", -1)) != 1:
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