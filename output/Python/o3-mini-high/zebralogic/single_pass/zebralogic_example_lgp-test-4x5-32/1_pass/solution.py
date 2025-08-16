#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    names = ["Arnold", "Alice", "Eric", "Peter"]
    hobbies = ["cooking", "painting", "photography", "gardening"]
    birthdays = ["april", "jan", "sept", "feb"]
    educations = ["master", "bachelor", "associate", "high school"]
    smoothies = ["cherry", "watermelon", "desert", "dragonfruit"]

    # The constraints:
    # - House indices: 0,1,2,3 correspond to houses 1-4.
    # - Clue 4: House3 (index 2) must have education "high school".
    # - Clue 9: House3 (index 2) must have birthday "sept".
    # - Clue 8: There is one house between the Dragonfruit smoothie lover and the person whose birthday is in September.
    #   Since house3 is "sept", the Dragonfruit smoothie lover must be in house1 (index 0).
    # - Clue 10: The person who loves cooking is Alice. (So in the house where name=="Alice", hobby=="cooking".)
    # - Clue 6: Arnold has an associate degree.
    # - Clue 2 & 3 & 1: Eric is the bachelor's, and the person with birthday "jan" is the bachelor's and also is the Desert smoothie lover.
    # - Clue 7 & 12: The person who paints is the one with a master's degree and birthday "feb". (That forces Peter.)
    # - Clue 11: The person with birthday "april" (Arnold) and the person who enjoys gardening are neighbors.
    #
    # We'll brute-force over all permutations with these filtering constraints.
    
    for names_perm in itertools.permutations(names):
        # Enforce: The person who loves cooking is Alice.
        idx_alice = names_perm.index("Alice")
        for hobbies_perm in itertools.permutations(hobbies):
            if hobbies_perm[idx_alice] != "cooking":
                continue

            for birthdays_perm in itertools.permutations(birthdays):
                # Enforce: House3 (index 2) must have birthday "sept" (clue 9)
                if birthdays_perm[2] != "sept":
                    continue

                for educations_perm in itertools.permutations(educations):
                    # Enforce: House3 (index 2) must have education "high school" (clue 4)
                    if educations_perm[2] != "high school":
                        continue

                    for smoothies_perm in itertools.permutations(smoothies):
                        # Enforce: House1 (index 0) must have the Dragonfruit smoothie (clue 8, since sept is in house3)
                        if smoothies_perm[0] != "dragonfruit":
                            continue
                        # Enforce: The Watermelon smoothie lover is not in house3 (clue 5)
                        if smoothies_perm[2] == "watermelon":
                            continue

                        valid = True
                        # Check each house's constraints individually.
                        for i in range(4):
                            name = names_perm[i]
                            hobby = hobbies_perm[i]
                            birthday = birthdays_perm[i]
                            education = educations_perm[i]
                            smoothie = smoothies_perm[i]

                            # Clue 1: The Desert smoothie lover is the person whose birthday is in January.
                            if smoothie == "desert" and birthday != "jan":
                                valid = False
                                break
                            # Clue 3: The person whose birthday is in January is the person with a bachelor's degree.
                            if birthday == "jan" and education != "bachelor":
                                valid = False
                                break
                            # Clue 7 & 12: The person who paints as a hobby is the person with a master's degree and birthday "feb".
                            if hobby == "painting":
                                if education != "master" or birthday != "feb":
                                    valid = False
                                    break

                        if not valid:
                            continue

                        # Check constraints based on specific persons:
                        for i in range(4):
                            name = names_perm[i]
                            hobby = hobbies_perm[i]
                            birthday = birthdays_perm[i]
                            education = educations_perm[i]
                            smoothie = smoothies_perm[i]
                            
                            if name == "Eric":
                                # Clue 2: Eric is the person with a bachelor's degree.
                                # Also, by clues 1 and 3, the bachelor's should have birthday "jan" and be the Desert smoothie lover.
                                if education != "bachelor" or birthday != "jan" or smoothie != "desert":
                                    valid = False
                                    break
                            if name == "Arnold":
                                # Clue 6: Arnold has an associate degree.
                                # And by elimination, his birthday must be "april" (since the other birthdays are taken by Eric, Alice, Peter).
                                if education != "associate" or birthday != "april":
                                    valid = False
                                    break
                            if name == "Peter":
                                # Clue 7 & 12 imply the painter (Peter) has a master's degree and birthday "feb".
                                if education != "master" or hobby != "painting" or birthday != "feb":
                                    valid = False
                                    break
                        if not valid:
                            continue

                        # Clue 11: The person whose birthday is in April and the person who enjoys gardening are next to each other.
                        try:
                            idx_arnold = names_perm.index("Arnold")
                        except ValueError:
                            valid = False
                        if valid:
                            neighbor_gardening = False
                            if idx_arnold > 0 and hobbies_perm[idx_arnold - 1] == "gardening":
                                neighbor_gardening = True
                            if idx_arnold < 3 and hobbies_perm[idx_arnold + 1] == "gardening":
                                neighbor_gardening = True
                            if not neighbor_gardening:
                                valid = False
                        if not valid:
                            continue

                        # All constraints satisfied; build and return the solution.
                        houses = []
                        for i in range(4):
                            house_num = str(i + 1)
                            row = [
                                house_num,
                                names_perm[i],
                                hobbies_perm[i],
                                birthdays_perm[i],
                                educations_perm[i],
                                smoothies_perm[i]
                            ]
                            houses.append(row)
                        return houses
    return None

def main():
    sol = solve_puzzle()
    result = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
            "rows": sol if sol is not None else []
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()