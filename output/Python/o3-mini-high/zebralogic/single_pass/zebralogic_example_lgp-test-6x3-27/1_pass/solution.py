#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    names_list = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"]
    occupations_list = ["engineer", "artist", "doctor", "teacher", "nurse", "lawyer"]
    cars_list = ["chevrolet silverado", "ford f150", "honda civic", "toyota camry", "bmw 3 series", "tesla model 3"]

    solution = None

    for names_perm in itertools.permutations(names_list):
        # Constraint 9: Carol is not in the sixth house.
        if names_perm[5] == "Carol":
            continue
        # Constraint 6: Carol is somewhere to the right of Eric.
        if names_perm.index("Carol") <= names_perm.index("Eric"):
            continue

        for occ_perm in itertools.permutations(occupations_list):
            # Constraint 7: The person who is a doctor is Eric.
            if occ_perm[names_perm.index("Eric")] != "doctor":
                continue
            # Constraint 10: The person who is an engineer is Bob.
            if occ_perm[names_perm.index("Bob")] != "engineer":
                continue
            # Constraint 14: Arnold is the person who is an artist.
            if occ_perm[names_perm.index("Arnold")] != "artist":
                continue
            # Constraint 4: The person who is a lawyer is not in the fifth house.
            if occ_perm[4] == "lawyer":
                continue
            # Constraint 8: The teacher is somewhere to the left of the nurse.
            pos_teacher = occ_perm.index("teacher")
            pos_nurse = occ_perm.index("nurse")
            if pos_teacher >= pos_nurse:
                continue
            # Constraint 5: The person who is a nurse is directly left of the person who is an artist.
            pos_arnold = names_perm.index("Arnold")
            if pos_arnold == 0:
                continue
            if occ_perm[pos_arnold - 1] != "nurse":
                continue

            for car_perm in itertools.permutations(cars_list):
                # Constraint 1: The person who owns a Ford F-150 is in the fifth house.
                if car_perm[4] != "ford f150":
                    continue
                # Constraint 2: The person who owns a Chevrolet Silverado is not in the second house.
                if car_perm[1] == "chevrolet silverado":
                    continue
                # Constraint 11: The person who owns a Toyota Camry is the person who is a nurse.
                valid_camry = True
                for i in range(6):
                    if car_perm[i] == "toyota camry" and occ_perm[i] != "nurse":
                        valid_camry = False
                        break
                    if occ_perm[i] == "nurse" and car_perm[i] != "toyota camry":
                        valid_camry = False
                        break
                if not valid_camry:
                    continue
                # Constraint 3: The person who owns a Honda Civic and Peter are next to each other.
                pos_peter = names_perm.index("Peter")
                pos_honda = car_perm.index("honda civic")
                if abs(pos_peter - pos_honda) != 1:
                    continue
                # Constraint 12: There is one house between Peter and the person who is a lawyer.
                pos_lawyer = occ_perm.index("lawyer")
                if abs(pos_peter - pos_lawyer) != 2:
                    continue
                # Constraint 13: There is one house between the person who owns a Tesla Model 3 and Bob.
                pos_bob = names_perm.index("Bob")
                pos_tesla = car_perm.index("tesla model 3")
                if abs(pos_tesla - pos_bob) != 2:
                    continue

                # All constraints satisfied; record the solution.
                solution = {"header": ["House", "Name", "Occupation", "CarModel"], "rows": []}
                for i in range(6):
                    solution["rows"].append([str(i+1), names_perm[i], occ_perm[i], car_perm[i]])
                return solution
    return solution

if __name__ == "__main__":
    sol = solve_puzzle()
    output = {"solution": sol}
    print(json.dumps(output, indent=2))