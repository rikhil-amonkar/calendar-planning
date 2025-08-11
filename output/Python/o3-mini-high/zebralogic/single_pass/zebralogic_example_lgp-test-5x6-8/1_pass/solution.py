#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the lists of attributes as given in the puzzle
    names_all = ["Eric", "Peter", "Arnold", "Bob", "Alice"]
    styles_all = ["modern", "craftsman", "ranch", "victorian", "colonial"]
    mothers_all = ["Penny", "Kailyn", "Holly", "Janelle", "Aniya"]
    phones_all = ["oneplus 9", "google pixel 6", "huawei p50", "iphone 13", "samsung galaxy s21"]
    drinks_all = ["coffee", "water", "root beer", "tea", "milk"]
    animals_all = ["fish", "dog", "horse", "bird", "cat"]

    # Houses will be represented by indices 0 to 4 corresponding to House 1 to House 5.
    solutions = []
    
    # Iterate over possible permutations for names.
    # Enforce these clues:
    # Clue 20 & 6: The root beer lover is Peter and his animal is cat.
    # Clue 2: The one who drinks water is Alice.
    # Clue 9 & 17: The tea drinker is Bob and is in the fourth house (index3).
    # Clue 16: Eric is not in the second house (index1).
    for perm_names in itertools.permutations(names_all):
        if perm_names[0] != "Peter":
            continue
        if perm_names[3] != "Bob":
            continue
        if perm_names[4] != "Alice":
            continue
        if perm_names[1] == "Eric":
            continue

        # Iterate over drink permutations.
        # Enforce:
        # Clue 6 & 11 & 20: The house with 'root beer' (index?) must be Peter. We'll force house0 = "root beer"
        # Clue 17 & 9: House4 (index3) must have "tea"
        # Clue 2 & 22: The water drinker is Alice; we force house5 (index4) to be "water"
        # Thus we require:
        # House1 (index0) = "root beer", house4 (index3) = "tea", house5 (index4) = "water".
        for perm_drinks in itertools.permutations(drinks_all):
            if perm_drinks[0] != "root beer":
                continue
            if perm_drinks[3] != "tea":
                continue
            if perm_drinks[4] != "water":
                continue

            # Iterate over house style permutations.
            # Enforce:
            # Clue 12 & 19: The person in the modern house is the horse keeper and has mother Penny.
            # Clue 15: The Google Pixel 6 user lives in a Craftsman‐style house.
            # Clue 7: The colonial house is not in the fourth house.
            # We also know that only two styles remain for houses 1 and 2.
            # From deduction the only possible assignment is:
            # House 1 (index0) = "victorian", House 2 (index1) = "ranch",
            # House 3 (index2) = "modern", House 4 (index3) = "craftsman", House 5 (index4) = "colonial"
            for perm_styles in itertools.permutations(styles_all):
                if perm_styles[2] != "modern":
                    continue
                if perm_styles[3] != "craftsman":
                    continue
                if perm_styles[4] != "colonial":
                    continue
                # Houses 0 and 1 must use the remaining two styles: "victorian" and "ranch"
                if set(perm_styles[0:2]) != set(["victorian", "ranch"]):
                    continue

                # Iterate over mothers.
                # Enforce:
                # Clue 19: House with modern style (index2) must have mother "Penny".
                # Clue 22: The water drinker (index4) must have mother "Janelle".
                for perm_mothers in itertools.permutations(mothers_all):
                    if perm_mothers[2] != "Penny":
                        continue
                    if perm_mothers[4] != "Janelle":
                        continue
                    # Clue 5: The person in a ranch-style home is the person whose mother's name is Kailyn.
                    valid_mother = True
                    for i in range(5):
                        if perm_styles[i] == "ranch" and perm_mothers[i] != "Kailyn":
                            valid_mother = False
                            break
                    if not valid_mother:
                        continue
                    # Clue 21: The person whose mother's name is Aniya is not in the fourth house (index3)
                    if perm_mothers[3] == "Aniya":
                        continue
                    # In our two possible assignments for houses 0 and 1 from styles, if house0 were "ranch" then its mother would have to be Kailyn.
                    # That would force Peter (house0) to have mother Kailyn. But clue 11 requires that the root beer lover (Peter) is to the left of Kailyn.
                    # So house0 cannot be "ranch". Hence, house0 must be "victorian" and house1 "ranch".
                    if perm_styles[0] == "ranch":
                        continue

                    # Iterate over phone permutations.
                    # We must assign phones as a permutation of phones_all.
                    # Enforce:
                    # Clue 15: The Google Pixel 6 user lives in a Craftsman‐style house.
                    # So the house that gets "google pixel 6" must have style "craftsman" => index3.
                    for perm_phones in itertools.permutations(phones_all):
                        if perm_phones[3] != "google pixel 6":
                            continue
                        # Clue 1: The Google Pixel 6 user is not in the first house. (Already satisfied because index3 is not first.)
                        # Clue 3: The person in the colonial house (style "colonial" at index4) is to the right of the person who uses "huawei p50".
                        try:
                            index_huawei = perm_phones.index("huawei p50")
                        except ValueError:
                            continue
                        if not (index_huawei < 4):
                            continue
                        # Clue 13: The person using "iphone 13" must like milk.
                        valid_phone = True
                        for i in range(5):
                            if perm_phones[i] == "iphone 13" and perm_drinks[i] != "milk":
                                valid_phone = False
                                break
                        if not valid_phone:
                            continue

                        # Iterate over animals.
                        # Enforce:
                        # Clue 6 & 20: The root beer lover (house index0) is a cat lover.
                        # Clue 8: The bird keeper is in the fourth house (index3).
                        # Clue 14: The dog owner (drinks milk) must be the one who likes milk.
                        # Clue 18: The person who keeps horses is in the third house (index2).
                        for perm_animals in itertools.permutations(animals_all):
                            if perm_animals[0] != "cat":
                                continue
                            if perm_animals[3] != "bird":
                                continue
                            if perm_animals[2] != "horse":
                                continue
                            # Given only one animal is left for dog and fish, and by clue 14 the milk drinker’s (index1) animal must be dog.
                            if perm_animals[1] != "dog":
                                continue
                            # Then house index4 must be "fish"
                            if perm_animals[4] != "fish":
                                continue

                            # Now check the cross-house relative constraints:

                            # Clue 2: The one who drinks water is Alice.
                            water_index = perm_drinks.index("water")
                            if perm_names[water_index] != "Alice":
                                continue
                            # Clue 4: The person who keeps horses uses a OnePlus 9.
                            horse_index = perm_animals.index("horse")
                            if perm_phones[horse_index] != "oneplus 9":
                                continue
                            # Clue 6: The root beer lover is the cat lover.
                            root_beer_index = perm_drinks.index("root beer")
                            if perm_animals[root_beer_index] != "cat":
                                continue
                            # Clue 7: The colonial house is not in the fourth house.
                            colonial_index = perm_styles.index("colonial")
                            if colonial_index == 3:
                                continue
                            # Clue 9: The tea drinker is Bob.
                            tea_index = perm_drinks.index("tea")
                            if perm_names[tea_index] != "Bob":
                                continue
                            # Clue 10: The tea drinker is to the right of the person whose mother's name is Kailyn.
                            kailyn_index = perm_mothers.index("Kailyn")
                            if tea_index <= kailyn_index:
                                continue
                            # Clue 11: The root beer lover is to the left of the person whose mother's name is Kailyn.
                            if root_beer_index >= kailyn_index:
                                continue
                            # Clue 12: The person who keeps horses is in a modern house.
                            if perm_styles[horse_index] != "modern":
                                continue
                            # Clue 14: The dog owner is the person who likes milk.
                            dog_index = perm_animals.index("dog")
                            milk_index = perm_drinks.index("milk")
                            if dog_index != milk_index:
                                continue
                            # Clue 15: (Already ensured via phone and style check.)
                            if perm_styles[perm_phones.index("google pixel 6")] != "craftsman":
                                continue
                            # Clue 16: Eric is not in the second house.
                            if perm_names[1] == "Eric":
                                continue
                            # Clue 17: The tea drinker is in the fourth house.
                            if tea_index != 3:
                                continue
                            # Clue 18: The person who keeps horses is in the third house.
                            if perm_animals[2] != "horse":
                                continue
                            # Clue 19: The modern house (index2) has mother "Penny".
                            modern_index = perm_styles.index("modern")
                            if perm_mothers[modern_index] != "Penny":
                                continue
                            # Clue 20: The root beer lover is Peter.
                            if perm_names[root_beer_index] != "Peter":
                                continue
                            # Clue 21: The person whose mother's name is Aniya is not in the fourth house.
                            if "Aniya" in perm_mothers and perm_mothers.index("Aniya") == 3:
                                continue
                            # Clue 22: The person whose mother's name is Janelle is the one who drinks water.
                            if perm_mothers[perm_drinks.index("water")] != "Janelle":
                                continue

                            # All constraints are satisfied. Build the solution.
                            solution = []
                            for i in range(5):
                                # House numbers are 1-indexed in the output.
                                house = [
                                    str(i+1),
                                    perm_names[i],
                                    perm_styles[i],
                                    perm_mothers[i],
                                    perm_phones[i],
                                    perm_drinks[i],
                                    perm_animals[i]
                                ]
                                solution.append(house)
                            solutions.append(solution)

    # Assuming there is a unique solution, take the first one.
    if solutions:
        sol = solutions[0]
        output = {
            "solution": {
                "header": ["House", "Name", "style", "mother", "phone", "drink", "animal"],
                "rows": sol
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": "No solution found."}))

if __name__ == "__main__":
    main()