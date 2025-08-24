import json
from itertools import permutations

def solve_puzzle():
    # Input variables (attributes and houses)
    houses = [1, 2, 3]
    names = ["Peter", "Eric", "Arnold"]
    educations = ["bachelor", "associate", "high school"]
    occupations = ["teacher", "doctor", "engineer"]

    def pos(seq, value):
        # Returns 1-based position
        return seq.index(value) + 1

    solutions = []

    # Enumerate all possible assignments
    for name_arr in permutations(names):
        for edu_arr in permutations(educations):
            for occ_arr in permutations(occupations):
                # Clue 1: teacher is directly left of associate
                if not (pos(occ_arr, "teacher") + 1 == pos(edu_arr, "associate")):
                    continue

                # Clue 2: associate and Eric are next to each other
                if abs(pos(edu_arr, "associate") - pos(name_arr, "Eric")) != 1:
                    continue

                # Clue 3: Peter has high school diploma
                if edu_arr[pos(name_arr.index("Peter"))] != "high school":
                    continue

                # Clue 4: doctor is the bachelor's degree holder
                if edu_arr[pos(occ_arr.index("doctor"))] != "bachelor":
                    continue

                # If all constraints satisfied, record solution
                rows = []
                for i, house in enumerate(houses):
                    rows.append([str(house), name_arr[i], edu_arr[i], occ_arr[i]])
                solutions.append(rows)

    # Choose the first solution (expected to be unique)
    if not solutions:
        raise ValueError("No solution found with the given constraints.")
    result_rows = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "Education", "Occupation"],
            "rows": result_rows
        }
    }
    return output

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))