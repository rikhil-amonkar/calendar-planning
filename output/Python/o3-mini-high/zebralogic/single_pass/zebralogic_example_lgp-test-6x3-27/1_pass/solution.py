#!/usr/bin/env python3
import itertools
import json
import sys

def main():
    names = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"]
    occupations = ["engineer", "artist", "doctor", "teacher", "nurse", "lawyer"]
    cars = ["chevrolet silverado", "ford f150", "honda civic", "toyota camry", "bmw 3 series", "tesla model 3"]

    # Precompute valid car permutations based on fixed car constraints:
    # Constraint 1: Ford F-150 is in the fifth house (index 4).
    # Constraint 2: Chevrolet Silverado is not in the second house (index 1).
    car_candidates = []
    for car_perm in itertools.permutations(cars):
        if car_perm[4] != "ford f150":
            continue
        if car_perm[1] == "chevrolet silverado":
            continue
        car_candidates.append(car_perm)

    # Iterate over all permutations of names
    for name_perm in itertools.permutations(names):
        # Constraint 9: Carol is not in the sixth house.
        if name_perm[5] == "Carol":
            continue
        # Constraint 6: Carol is somewhere to the right of Eric.
        if name_perm.index("Carol") <= name_perm.index("Eric"):
            continue

        # Iterate over all permutations of occupations
        for occ_perm in itertools.permutations(occupations):
            # Constraint 7: The person who is a doctor is Eric.
            if occ_perm[name_perm.index("Eric")] != "doctor":
                continue
            # Constraint 10: The person who is an engineer is Bob.
            if occ_perm[name_perm.index("Bob")] != "engineer":
                continue
            # Constraint 14: Arnold is the person who is an artist.
            if occ_perm[name_perm.index("Arnold")] != "artist":
                continue
            # Constraint 5: The person who is a nurse is directly left of the person who is an artist.
            arnie_index = name_perm.index("Arnold")
            if arnie_index == 0:
                continue
            if occ_perm[arnie_index - 1] != "nurse":
                continue
            # Constraint 8: The person who is a teacher is somewhere to the left of the person who is a nurse.
            try:
                teacher_index = occ_perm.index("teacher")
                nurse_index = occ_perm.index("nurse")
            except ValueError:
                continue
            if teacher_index >= nurse_index:
                continue
            # Constraint 4: The person who is a lawyer is not in the fifth house.
            if occ_perm[4] == "lawyer":
                continue
            # Constraint 12: There is one house between Peter and the person who is a lawyer.
            if abs(name_perm.index("Peter") - occ_perm.index("lawyer")) != 2:
                continue

            # Iterate over precomputed car candidates
            for car_perm in car_candidates:
                # Constraint 11: The person who owns a Toyota Camry is the person who is a nurse.
                try:
                    camry_index = car_perm.index("toyota camry")
                except ValueError:
                    continue
                if occ_perm[camry_index] != "nurse":
                    continue

                # Constraint 13: There is one house between the person who owns a Tesla Model 3 and Bob.
                try:
                    tesla_index = car_perm.index("tesla model 3")
                except ValueError:
                    continue
                if abs(tesla_index - name_perm.index("Bob")) != 2:
                    continue

                # Constraint 3: The person who owns a Honda Civic and Peter are next to each other.
                try:
                    civic_index = car_perm.index("honda civic")
                except ValueError:
                    continue
                if abs(civic_index - name_perm.index("Peter")) != 1:
                    continue

                # If we reached here, all constraints are satisfied.
                solution = {
                    "solution": {
                        "header": ["House", "Name", "occupation", "car"],
                        "rows": []
                    }
                }
                for i in range(6):
                    solution["solution"]["rows"].append([
                        str(i+1),
                        name_perm[i],
                        occ_perm[i],
                        car_perm[i]
                    ])
                print(json.dumps(solution))
                sys.exit(0)

if __name__ == "__main__":
    main()