import itertools
import json

def solve_puzzle():
    # Define possible attributes
    names = ["Arnold", "Peter", "Eric"]
    occupations = ["doctor", "teacher", "engineer"]
    educations = ["associate", "high school", "bachelor"]
    smoothies = ["desert", "cherry", "watermelon"]
    hobbies = ["gardening", "cooking", "photography"]

    solutions = []

    # Houses are indexed 0, 1, 2 corresponding to House 1, House 2, House 3
    for names_perm in itertools.permutations(names):
        # Clue 2: Arnold is not in the third house (index 2)
        if names_perm[2] == "Arnold":
            continue
        # Clue 5: The person who loves cooking is Peter.
        # Clue 4: Cooking hobby is in the second house, so enforce that names_perm[1] must be Peter.
        if names_perm[1] != "Peter":
            continue

        for occ_perm in itertools.permutations(occupations):
            # Clue 8: The person who loves cooking is the person who is a doctor.
            # And since cooking is in the second house (index 1), occupation for house 2 must be doctor.
            if occ_perm[1] != "doctor":
                continue

            for edu_perm in itertools.permutations(educations):
                for smoothie_perm in itertools.permutations(smoothies):
                    for hobby_perm in itertools.permutations(hobbies):
                        # Clue 3: The person who likes Cherry smoothies is somewhere to the right of Peter.
                        # Peter is in house 2 (index 1), so the index of "cherry" must be > 1.
                        if smoothie_perm.index("cherry") <= names_perm.index("Peter"):
                            continue

                        # Clue 4: The person who loves cooking is in the second house.
                        if hobby_perm[1] != "cooking":
                            continue

                        # Clue 5: The person who loves cooking is Peter.
                        if names_perm[hobby_perm.index("cooking")] != "Peter":
                            continue

                        # Clue 6: The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
                        if edu_perm.index("associate") <= hobby_perm.index("gardening"):
                            continue

                        # Clue 7: The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
                        if edu_perm.index("bachelor") <= smoothie_perm.index("desert"):
                            continue

                        # Clue 8: The person who loves cooking is the person who is a doctor.
                        if occ_perm[hobby_perm.index("cooking")] != "doctor":
                            continue

                        # Clue 9: The photography enthusiast is the person who is a teacher.
                        if occ_perm[hobby_perm.index("photography")] != "teacher":
                            continue

                        # Clue 1: The Desert smoothie lover is the person who is a doctor.
                        if occ_perm[smoothie_perm.index("desert")] != "doctor":
                            continue

                        # If all constraints are satisfied, record the solution.
                        solution = []
                        for i in range(3):
                            # House numbers are 1-indexed in the output.
                            house_row = [
                                str(i + 1),
                                names_perm[i],
                                occ_perm[i],
                                edu_perm[i],
                                smoothie_perm[i],
                                hobby_perm[i]
                            ]
                            solution.append(house_row)
                        solutions.append(solution)

    return solutions

def main():
    sol = solve_puzzle()
    if sol:
        # We take the first valid solution found.
        result = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
                "rows": sol[0]
            }
        }
    else:
        result = {"solution": {"header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"], "rows": []}}
    print(json.dumps(result))

if __name__ == "__main__":
    main()