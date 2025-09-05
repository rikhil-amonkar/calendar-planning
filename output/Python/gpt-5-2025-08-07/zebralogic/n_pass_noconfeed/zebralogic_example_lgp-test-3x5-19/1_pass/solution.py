import json
from itertools import permutations

def solve_puzzle():
    houses = [0, 1, 2]  # indices for houses 1..3

    Names = ["Arnold", "Peter", "Eric"]
    Occupations = ["doctor", "teacher", "engineer"]
    Educations = ["associate", "high school", "bachelor"]
    Smoothies = ["desert", "cherry", "watermelon"]
    Hobbies = ["gardening", "cooking", "photography"]

    solutions = []

    for name_perm in permutations(Names):
        # Clue 2: Arnold is not in the third house.
        if name_perm[2] == "Arnold":
            continue
        # Clue 5 + 4: The person who loves cooking is Peter, and cooking is in the second house.
        # Therefore, Peter must be in the second house.
        if name_perm[1] != "Peter":
            continue

        for hobby_perm in permutations(Hobbies):
            # Clue 4: The person who loves cooking is in the second house.
            if hobby_perm[1] != "cooking":
                continue

            for occ_perm in permutations(Occupations):
                # Clue 8: The person who loves cooking is the person who is a doctor.
                if occ_perm[1] != "doctor":
                    continue

                # Clue 9: The photography enthusiast is the person who is a teacher. (bi-directional)
                ok = True
                for i in houses:
                    if (hobby_perm[i] == "photography") != (occ_perm[i] == "teacher"):
                        ok = False
                        break
                if not ok:
                    continue

                for smoothie_perm in permutations(Smoothies):
                    # Clue 1: The Desert smoothie lover is the person who is a doctor. (bi-directional)
                    ok = True
                    for i in houses:
                        if (smoothie_perm[i] == "desert") != (occ_perm[i] == "doctor"):
                            ok = False
                            break
                    if not ok:
                        continue

                    # Clue 3: The person who likes Cherry smoothies is somewhere to the right of Peter.
                    idx_peter = name_perm.index("Peter")
                    idx_cherry = smoothie_perm.index("cherry")
                    if not (idx_cherry > idx_peter):
                        continue

                    for edu_perm in permutations(Educations):
                        # Clue 7: The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
                        idx_bachelor = edu_perm.index("bachelor")
                        idx_desert = smoothie_perm.index("desert")
                        if not (idx_bachelor > idx_desert):
                            continue

                        # Clue 6: The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
                        idx_associate = edu_perm.index("associate")
                        idx_gardening = hobby_perm.index("gardening")
                        if not (idx_associate > idx_gardening):
                            continue

                        # Clue 8 again (bi-directional check): cooking <-> doctor
                        ok2 = True
                        for i in houses:
                            if (hobby_perm[i] == "cooking") != (occ_perm[i] == "doctor"):
                                ok2 = False
                                break
                        if not ok2:
                            continue

                        # All constraints satisfied; record solution
                        solutions.append((name_perm, occ_perm, edu_perm, smoothie_perm, hobby_perm))

    if not solutions:
        raise RuntimeError("No solution found.")

    # Choose the first (should be unique)
    name_perm, occ_perm, edu_perm, smoothie_perm, hobby_perm = solutions[0]

    header = ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"]
    rows = []
    for i in houses:
        row = [
            str(i + 1),
            name_perm[i],
            occ_perm[i],
            edu_perm[i],
            smoothie_perm[i],
            hobby_perm[i],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))