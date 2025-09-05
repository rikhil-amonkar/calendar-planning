import itertools
import json

def solve_puzzle():
    names = ["Peter", "Eric", "Arnold"]
    educations = ["bachelor", "associate", "high school"]
    occupations = ["teacher", "doctor", "engineer"]

    for name_perm in itertools.permutations(names):
        for edu_perm in itertools.permutations(educations):
            for occ_perm in itertools.permutations(occupations):
                # Clue 1: The teacher is directly left of the person with an associate's degree.
                teacher_index = occ_perm.index("teacher")
                # Teacher cannot be in the rightmost house
                if teacher_index == 2:
                    continue
                if edu_perm[teacher_index + 1] != "associate":
                    continue

                # Clue 2: The person with an associate's degree and Eric are next to each other.
                associate_index = edu_perm.index("associate")
                eric_index = name_perm.index("Eric")
                if abs(associate_index - eric_index) != 1:
                    continue

                # Clue 3: Peter is the person with a high school diploma.
                peter_index = name_perm.index("Peter")
                if edu_perm[peter_index] != "high school":
                    continue

                # Clue 4: The person who is a doctor is the person with a bachelor's degree.
                doctor_index = occ_perm.index("doctor")
                if edu_perm[doctor_index] != "bachelor":
                    continue

                solution = {
                    "header": ["House", "Name", "Education", "Occupation"],
                    "rows": []
                }
                for i in range(3):
                    house_number = str(i + 1)
                    row = [house_number, name_perm[i], edu_perm[i], occ_perm[i]]
                    solution["rows"].append(row)
                return solution
    return None

if __name__ == "__main__":
    sol = solve_puzzle()
    output = {"solution": sol}
    print(json.dumps(output, indent=2))