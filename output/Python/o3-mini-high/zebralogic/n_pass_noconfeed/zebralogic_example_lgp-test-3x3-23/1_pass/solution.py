#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Peter", "Arnold", "Eric"]
    occupations = ["doctor", "teacher", "engineer"]
    hobbies = ["cooking", "photography", "gardening"]
    
    # Houses are indexed 0, 1, 2 corresponding to House "1", "2", "3"
    for name_perm in itertools.permutations(names):
        for occ_perm in itertools.permutations(occupations):
            for hobby_perm in itertools.permutations(hobbies):
                valid = True
                
                # Constraint 5: The person who is an engineer is Peter.
                for i in range(3):
                    if occ_perm[i] == "engineer" and name_perm[i] != "Peter":
                        valid = False
                        break
                    if name_perm[i] == "Peter" and occ_perm[i] != "engineer":
                        valid = False
                        break
                if not valid:
                    continue
                
                # Constraint 4: The photography enthusiast is the person who is a teacher.
                for i in range(3):
                    if hobby_perm[i] == "photography" and occ_perm[i] != "teacher":
                        valid = False
                        break
                    if occ_perm[i] == "teacher" and hobby_perm[i] != "photography":
                        valid = False
                        break
                if not valid:
                    continue
                
                # Constraint 2: The person who loves cooking is directly left of the teacher.
                teacher_index = None
                for i in range(3):
                    if occ_perm[i] == "teacher":
                        teacher_index = i
                        break
                # Teacher cannot be in the first house because then no house is to his left.
                if teacher_index is None or teacher_index == 0:
                    continue
                if hobby_perm[teacher_index - 1] != "cooking":
                    continue
                
                # Constraint 1: The person who is a doctor and Eric are next to each other.
                doctor_index = None
                for i in range(3):
                    if occ_perm[i] == "doctor":
                        doctor_index = i
                        break
                if doctor_index is None:
                    continue
                if not ((doctor_index > 0 and name_perm[doctor_index - 1] == "Eric") or 
                        (doctor_index < 2 and name_perm[doctor_index + 1] == "Eric")):
                    continue
                
                # Constraint 3: The doctor is somewhere to the right of the person who enjoys gardening.
                gardening_index = None
                for i in range(3):
                    if hobby_perm[i] == "gardening":
                        gardening_index = i
                        break
                if gardening_index is None or doctor_index <= gardening_index:
                    continue
                
                # If we reach this point, we have a valid solution.
                rows = []
                for i in range(3):
                    house_number = str(i + 1)
                    rows.append([house_number, name_perm[i], occ_perm[i], hobby_perm[i]])
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Occupation", "Hobby"],
                        "rows": rows
                    }
                }
                print(json.dumps(solution))
                return

if __name__ == "__main__":
    main()