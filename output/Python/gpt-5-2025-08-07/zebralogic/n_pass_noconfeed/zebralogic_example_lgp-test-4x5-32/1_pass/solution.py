import json
from itertools import permutations

def solve_puzzle():
    houses = [0, 1, 2, 3]  # indices for houses 1..4

    names = ["Arnold", "Alice", "Eric", "Peter"]
    hobbies = ["cooking", "painting", "photography", "gardening"]
    birthdays = ["april", "jan", "sept", "feb"]
    educations = ["master", "bachelor", "associate", "high school"]
    smoothies = ["cherry", "watermelon", "desert", "dragonfruit"]

    def pos(seq, value):
        return seq.index(value)

    solutions = []

    # Iterate over possible assignments with pruning at each step
    for bday in permutations(birthdays):
        # Clue 9 + 4: high school is the person whose birthday is in September and is in the third house
        # So birthday at house 3 (index 2) is 'sept'
        if bday[2] != "sept":
            continue

        for edu in permutations(educations):
            # Education at house 3 is 'high school'
            if edu[2] != "high school":
                continue

            # Clue 3: 'jan' == 'bachelor'
            if pos(bday, "jan") != pos(edu, "bachelor"):
                continue

            for sm in permutations(smoothies):
                # Clue 5: Watermelon smoothie lover is not in the third house
                if sm[2] == "watermelon":
                    continue

                # Clue 8: One house between Dragonfruit and September
                if abs(pos(sm, "dragonfruit") - pos(bday, "sept")) != 2:
                    continue

                # Clue 1: Desert smoothie lover is Jan birthday
                if pos(sm, "desert") != pos(bday, "jan"):
                    continue

                for nm in permutations(names):
                    # Clue 2: Eric has a bachelor's degree
                    if pos(nm, "Eric") != pos(edu, "bachelor"):
                        continue

                    # Clue 6: Arnold has an associate's degree
                    if pos(nm, "Arnold") != pos(edu, "associate"):
                        continue

                    for hb in permutations(hobbies):
                        # Clue 7: Master's degree is the person who paints
                        if pos(edu, "master") != pos(hb, "painting"):
                            continue

                        # Clue 12: Painter has birthday in February
                        if pos(hb, "painting") != pos(bday, "feb"):
                            continue

                        # Clue 10: Alice loves cooking
                        if pos(nm, "Alice") != pos(hb, "cooking"):
                            continue

                        # Clue 11: April and Gardening are next to each other
                        if abs(pos(bday, "april") - pos(hb, "gardening")) != 1:
                            continue

                        # All constraints satisfied, record solution
                        solutions.append((nm, hb, bday, edu, sm))

    if not solutions:
        raise RuntimeError("No solution found")

    # Choose the first solution (should be unique for a well-posed puzzle)
    nm, hb, bday, edu, sm = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
            "rows": []
        }
    }

    for i in range(4):
        row = [
            str(i + 1),
            nm[i],
            hb[i],
            bday[i],
            edu[i],
            sm[i]
        ]
        result["solution"]["rows"].append(row)

    print(json.dumps(result, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_puzzle()