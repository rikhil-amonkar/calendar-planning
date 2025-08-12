import itertools
import json

# Define the possible values for each category
names = ["Arnold", "Eric", "Alice", "Bob", "Peter"]
vacations = ["mountain", "city", "cruise", "beach", "camping"]
educations = ["doctorate", "high school", "bachelor", "associate", "master"]
colors = ["blue", "red", "white", "yellow", "green"]
phones = ["google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"]
lunches = ["grilled cheese", "stir fry", "pizza", "spaghetti", "stew"]

# Generate all possible permutations
permutations = list(itertools.permutations(range(5)))

def is_valid_solution(solution):
    # Unpack the solution into separate lists
    name_order = [solution[i][0] for i in range(5)]
    vacation_order = [solution[i][1] for i in range(5)]
    education_order = [solution[i][2] for i in range(5)]
    color_order = [solution[i][3] for i in range(5)]
    phone_order = [solution[i][4] for i in range(5)]
    lunch_order = [solution[i][5] for i in range(5)]

    # Check each clue
    if lunch_order[0] == "stew":
        return False
    if abs(lunch_order.index("stir fry") - education_order.index("associate")) != 2:
        return False
    if education_order[vacation_order.index("mountain")] != "bachelor":
        return False
    if name_order.index("Bob") >= education_order.index("doctorate"):
        return False
    if phone_order[2] != "samsung galaxy s21":
        return False
    if name_order[education_order.index("doctorate")] != "Eric":
        return False
    if education_order.index("doctorate") != 2:
        return False
    if lunch_order[vacation_order.index("stir fry")] != "bachelor":
        return False
    if lunch_order[education_order.index("doctorate")] != "pizza":
        return False
    if color_order.index("green") < name_order.index("Peter"):
        return False
    if vacation_order.index("camping") != phone_order.index("iphone 13"):
        return False
    if name_order[vacation_order.index("cruise")] != "Alice":
        return False
    if abs(phone_order.index("high school") - phone_order.index("samsung galaxy s21")) != 1:
        return False
    if name_order[phone_order.index("google pixel 6")] != "Arnold":
        return False
    if phone_order.index("oneplus 9") < phone_order.index("huawei p50"):
        return False
    if lunch_order[name_order.index("Arnold")] != "grilled cheese":
        return False
    if lunch_order.index("grilled cheese") == 3:
        return False
    if abs(education_order.index("bachelor") - color_order.index("red")) != 2:
        return False
    if vacation_order.index("beach") < vacation_order.index("city"):
        return False
    if color_order[1] == "green":
        return False
    if color_order.index("blue") < name_order.index("Peter"):
        return False
    if abs(vacation_order.index("camping") - color_order.index("yellow")) != 1:
        return False
    
    return True

# Try all permutations
for name_perm in permutations:
    for vacation_perm in permutations:
        for education_perm in permutations:
            for color_perm in permutations:
                for phone_perm in permutations:
                    for lunch_perm in permutations:
                        solution = [
                            (names[name_perm[0]], vacations[vacation_perm[0]], educations[education_perm[0]], colors[color_perm[0]], phones[phone_perm[0]], lunches[lunch_perm[0]]),
                            (names[name_perm[1]], vacations[vacation_perm[1]], educations[education_perm[1]], colors[color_perm[1]], phones[phone_perm[1]], lunches[lunch_perm[1]]),
                            (names[name_perm[2]], vacations[vacation_perm[2]], educations[education_perm[2]], colors[color_perm[2]], phones[phone_perm[2]], lunches[lunch_perm[2]]),
                            (names[name_perm[3]], vacations[vacation_perm[3]], educations[education_perm[3]], colors[color_perm[3]], phones[phone_perm[3]], lunches[lunch_perm[3]]),
                            (names[name_perm[4]], vacations[vacation_perm[4]], educations[education_perm[4]], colors[color_perm[4]], phones[phone_perm[4]], lunches[lunch_perm[4]])
                        ]
                        if is_valid_solution(solution):
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Vacation", "Education", "Color", "Phone", "Lunch"],
                                    "rows": [
                                        ["1", solution[0][0], solution[0][1], solution[0][2], solution[0][3], solution[0][4], solution[0][5]],
                                        ["2", solution[1][0], solution[1][1], solution[1][2], solution[1][3], solution[1][4], solution[1][5]],
                                        ["3", solution[2][0], solution[2][1], solution[2][2], solution[2][3], solution[2][4], solution[2][5]],
                                        ["4", solution[3][0], solution[3][1], solution[3][2], solution[3][3], solution[3][4], solution[3][5]],
                                        ["5", solution[4][0], solution[4][1], solution[4][2], solution[4][3], solution[4][4], solution[4][5]]
                                    ]
                                }
                            }
                            print(json.dumps(result, indent=2))
                            exit()