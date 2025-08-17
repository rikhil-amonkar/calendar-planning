import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Arnold", "Eric", "Alice", "Bob", "Peter"]
    vacations = ["mountain", "city", "cruise", "beach", "camping"]
    educations = ["doctorate", "high school", "bachelor", "associate", "master"]
    colors = ["blue", "red", "white", "yellow", "green"]
    phones = ["google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"]
    foods = ["grilled cheese", "stir fry", "pizza", "spaghetti", "stew"]

    all_combinations = list(itertools.permutations(range(5)))

    for name_order in all_combinations:
        for vacation_order in all_combinations:
            for education_order in all_combinations:
                for color_order in all_combinations:
                    for phone_order in all_combinations:
                        for food_order in all_combinations:
                            # Assign values based on order
                            name_map = {names[i]: i + 1 for i in name_order}
                            vacation_map = {vacations[i]: i + 1 for i in vacation_order}
                            education_map = {educations[i]: i + 1 for i in education_order}
                            color_map = {colors[i]: i + 1 for i in color_order}
                            phone_map = {phones[i]: i + 1 for i in phone_order}
                            food_map = {foods[i]: i + 1 for i in food_order}

                            # Check constraints
                            if (food_map["stew"] != 1 and
                                abs(food_map["stir fry"] - education_map["associate"]) == 3 and
                                education_map["bachelor"] == vacation_map["mountain"] and
                                name_map["Bob"] < education_map["doctorate"] and
                                phone_map["samsung galaxy s21"] == 3 and
                                name_map["Eric"] == education_map["doctorate"] and
                                education_map["doctorate"] == 3 and
                                food_map["stir fry"] == education_map["bachelor"] and
                                education_map["doctorate"] == food_map["pizza"] and
                                color_map["green"] > name_map["Peter"] and
                                vacation_map["camping"] == phone_map["iphone 13"] and
                                name_map["Alice"] == vacation_map["cruise"] and
                                abs(phone_map["samsung galaxy s21"] - education_map["high school"]) == 1 and
                                name_map["Arnold"] == phone_map["google pixel 6"] and
                                food_map["grilled cheese"] == name_map["Arnold"] and
                                food_map["grilled cheese"] != 4 and
                                abs(education_map["bachelor"] - color_map["red"]) == 3 and
                                vacation_map["beach"] > vacation_map["city"] and
                                color_map["green"] != 2 and
                                color_map["blue"] > name_map["Peter"] and
                                abs(vacation_map["camping"] - color_map["yellow"]) == 1):

                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],
                                        "rows": []
                                    }
                                }

                                for house in houses:
                                    name = names[name_order[house - 1]]
                                    vacation = vacations[vacation_order[house - 1]]
                                    education = educations[education_order[house - 1]]
                                    color = colors[color_order[house - 1]]
                                    phone = phones[phone_order[house - 1]]
                                    food = foods[food_order[house - 1]]

                                    solution["solution"]["rows"].append([
                                        str(house),
                                        name,
                                        vacation,
                                        education,
                                        color,
                                        phone,
                                        food
                                    ])

                                return json.dumps(solution, indent=2)

print(solve_puzzle())