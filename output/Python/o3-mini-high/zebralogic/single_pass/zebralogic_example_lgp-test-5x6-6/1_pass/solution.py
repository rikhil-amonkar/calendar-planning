#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Arnold", "Eric", "Alice", "Bob", "Peter"]
    vacations = ["mountain", "city", "cruise", "beach", "camping"]
    educations = ["doctorate", "high school", "bachelor", "associate", "master"]
    colors = ["blue", "red", "white", "yellow", "green"]
    phones = ["google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"]
    foods = ["grilled cheese", "stir fry", "pizza", "spaghetti", "stew"]

    # Iterate over all permutations with early constraints.
    for names_perm in itertools.permutations(names):
        # Constraint: House3 (index 2) must be Eric.
        if names_perm[2] != "Eric":
            continue
        # Bob must be to the left of House3 => index of Bob must be 0 or 1.
        if names_perm.index("Bob") > 1:
            continue
        # Arnold cannot be in House4 (index 3) because grilled cheese must not be in fourth house.
        if names_perm[3] == "Arnold":
            continue

        for edu_perm in itertools.permutations(educations):
            # Constraint: House3 must have doctorate.
            if edu_perm[2] != "doctorate":
                continue
            # High school must be exactly one house away from House3 (i.e. index 0 or 4)
            if edu_perm.index("high school") not in [0, 4]:
                continue

            for phone_perm in itertools.permutations(phones):
                # Constraint: House3 uses samsung galaxy s21.
                if phone_perm[2] != "samsung galaxy s21":
                    continue
                # Constraint: Arnold uses google pixel 6.
                valid_arnold_phone = True
                for i in range(5):
                    if names_perm[i] == "Arnold" and phone_perm[i] != "google pixel 6":
                        valid_arnold_phone = False
                        break
                if not valid_arnold_phone:
                    continue
                # Clue 15: oneplus 9 is somewhere to the right of huawei p50.
                if phone_perm.index("oneplus 9") <= phone_perm.index("huawei p50"):
                    continue

                for food_perm in itertools.permutations(foods):
                    # House3 food must be pizza (doctorate -> pizza)
                    if food_perm[2] != "pizza":
                        continue
                    # Clue 1: The stew lover is not in the first house.
                    if food_perm[0] == "stew":
                        continue
                    # Constraint: Arnold loves grilled cheese.
                    valid_arnold_food = True
                    for i in range(5):
                        if names_perm[i] == "Arnold" and food_perm[i] != "grilled cheese":
                            valid_arnold_food = False
                            break
                    if not valid_arnold_food:
                        continue
                    # Clue 8: The person who loves stir fry is the one with a bachelor's degree.
                    # So the house with bachelor must have food "stir fry".
                    valid_bachelor_food = True
                    for i in range(5):
                        if edu_perm[i] == "bachelor" and food_perm[i] != "stir fry":
                            valid_bachelor_food = False
                            break
                    if not valid_bachelor_food:
                        continue
                    # Clue 2: There are two houses between the stir fry lover and the person with an associate's degree.
                    try:
                        index_stir = food_perm.index("stir fry")
                        index_assoc = edu_perm.index("associate")
                    except ValueError:
                        continue
                    if abs(index_stir - index_assoc) != 3:
                        continue

                    for vac_perm in itertools.permutations(vacations):
                        # Clue 12: Alice loves cruises.
                        alice_index = names_perm.index("Alice")
                        if vac_perm[alice_index] != "cruise":
                            continue
                        # Clue 3: The person who enjoys mountain retreats is the one with a bachelor's degree.
                        valid_bachelor_vac = True
                        for i in range(5):
                            if edu_perm[i] == "bachelor" and vac_perm[i] != "mountain":
                                valid_bachelor_vac = False
                                break
                        if not valid_bachelor_vac:
                            continue
                        # Clue 11: The person who enjoys camping trips uses an iPhone 13.
                        valid_camping_phone = True
                        for i in range(5):
                            if vac_perm[i] == "camping" and phone_perm[i] != "iphone 13":
                                valid_camping_phone = False
                                break
                        if not valid_camping_phone:
                            continue
                        # Clue 19: The person who loves beach vacations is somewhere to the right of the person who prefers city breaks.
                        if vac_perm.index("beach") <= vac_perm.index("city"):
                            continue

                        for col_perm in itertools.permutations(colors):
                            # Clue 18: There are two houses between the bachelor and the red color.
                            if abs(edu_perm.index("bachelor") - col_perm.index("red")) != 3:
                                continue
                            # Clue 10: The green lover lives to the right of Peter.
                            index_peter = names_perm.index("Peter")
                            if col_perm.index("green") <= index_peter:
                                continue
                            # Clue 20: The person whose favorite color is green is not in the second house.
                            if col_perm[1] == "green":
                                continue
                            # Clue 21: The person whose favorite color is blue is somewhere to the right of Peter.
                            if col_perm.index("blue") <= index_peter:
                                continue
                            # Clue 22: There is one house between the person who enjoys camping trips and the person who loves yellow.
                            if abs(vac_perm.index("camping") - col_perm.index("yellow")) != 2:
                                continue

                            # All constraints satisfied; build the solution.
                            solution_rows = []
                            for i in range(5):
                                house_number = str(i+1)
                                row = [
                                    house_number,
                                    names_perm[i],
                                    vac_perm[i],
                                    edu_perm[i],
                                    col_perm[i],
                                    phone_perm[i],
                                    food_perm[i]
                                ]
                                solution_rows.append(row)
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],
                                    "rows": solution_rows
                                }
                            }
                            print(json.dumps(result, indent=2))
                            return

if __name__ == "__main__":
    main()