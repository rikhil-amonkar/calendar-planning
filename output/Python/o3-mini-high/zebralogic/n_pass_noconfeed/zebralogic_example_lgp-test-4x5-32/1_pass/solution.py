import itertools
import json

def main():
    names_list = ["Arnold", "Alice", "Eric", "Peter"]
    birthdays_list = ["april", "jan", "sept", "feb"]
    educations_list = ["master", "bachelor", "associate", "high school"]
    hobbies_list = ["cooking", "painting", "photography", "gardening"]
    smoothies_list = ["cherry", "watermelon", "desert", "dragonfruit"]

    solution = None

    for names in itertools.permutations(names_list):
        # Clue 10 and our deductions: The cooking lover is Alice.
        # Also by our reasoning, house 3 (index 2) must be occupied by Alice.
        if names[2] != "Alice":
            continue

        for birthdays in itertools.permutations(birthdays_list):
            # Clue 9: The person with a high school diploma (in house 3) has birthday sept.
            if birthdays[2] != "sept":
                continue

            for educations in itertools.permutations(educations_list):
                # Clue 4: The person with a high school diploma is in the third house.
                if educations[2] != "high school":
                    continue

                for hobbies in itertools.permutations(hobbies_list):
                    # Clue 10: The person who loves cooking is Alice.
                    # Since we already fixed house 3 (index 2) to be Alice, her hobby must be cooking.
                    if hobbies[2] != "cooking":
                        continue

                    for smoothies in itertools.permutations(smoothies_list):
                        # Clue 8 deduction: Since sept is in house 3 (index 2),
                        # the Dragonfruit smoothie lover must be exactly 2 houses away.
                        # With 4 houses, only possibility is house 1 (index 0).
                        if smoothies[0] != "dragonfruit":
                            continue
                        # Clue 5: The Watermelon smoothie lover is not in the third house.
                        if smoothies[2] == "watermelon":
                            continue

                        # Clue 1: The Desert smoothie lover is the person whose birthday is in January.
                        if smoothies.index("desert") != birthdays.index("jan"):
                            continue

                        # Clue 2: Eric is the person with a bachelor's degree.
                        if educations[names.index("Eric")] != "bachelor":
                            continue

                        # Clue 3: The person whose birthday is in January is the person with a bachelor's degree.
                        if birthdays.index("jan") != educations.index("bachelor"):
                            continue

                        # Clue 6: The person with an associate's degree is Arnold.
                        if educations[names.index("Arnold")] != "associate":
                            continue

                        # Clue 7: The person with a master's degree is the person who paints as a hobby.
                        valid_master_painting = True
                        for i in range(4):
                            if (educations[i] == "master" and hobbies[i] != "painting") or \
                               (hobbies[i] == "painting" and educations[i] != "master"):
                                valid_master_painting = False
                                break
                        if not valid_master_painting:
                            continue

                        # Clue 8: There is one house between the Dragonfruit smoothie lover and the person whose birthday is in September.
                        if abs(smoothies.index("dragonfruit") - birthdays.index("sept")) != 2:
                            continue

                        # Clue 9: The person with a high school diploma is the person whose birthday is in September.
                        if educations.index("high school") != birthdays.index("sept"):
                            continue

                        # Clue 10: The person who loves cooking is Alice.
                        if names[hobbies.index("cooking")] != "Alice":
                            continue

                        # Clue 11: The person whose birthday is in April and the person who enjoys gardening are next to each other.
                        if abs(birthdays.index("april") - hobbies.index("gardening")) != 1:
                            continue

                        # Clue 12: The person who paints as a hobby is the person whose birthday is in February.
                        if birthdays[hobbies.index("painting")] != "feb":
                            continue
                        if hobbies[birthdays.index("feb")] != "painting":
                            continue

                        # If all constraints are met, record the solution.
                        sol = {
                            "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
                            "rows": []
                        }
                        for i in range(4):
                            # Houses are numbered 1 to 4.
                            row = [str(i + 1), names[i], hobbies[i], birthdays[i], educations[i], smoothies[i]]
                            sol["rows"].append(row)
                        solution = {"solution": sol}
                        print(json.dumps(solution, indent=2))
                        return

if __name__ == "__main__":
    main()