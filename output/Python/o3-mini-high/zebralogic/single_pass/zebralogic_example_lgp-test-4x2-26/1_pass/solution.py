#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Arnold", "Eric", "Peter", "Alice"]
    occupations = ["doctor", "engineer", "artist", "teacher"]

    # We'll iterate over all assignments of names and occupations to houses.
    for name_perm in itertools.permutations(names):
        # Constraint 3: Peter is not in the first house.
        if name_perm[0] == "Peter":
            continue

        for occ_perm in itertools.permutations(occupations):
            # Constraint 2: The person who is a teacher is Peter.
            teacher_index = occ_perm.index("teacher")
            if name_perm[teacher_index] != "Peter":
                continue

            # Constraint 5: The person who is an artist is Alice.
            alice_index = name_perm.index("Alice")
            if occ_perm[alice_index] != "artist":
                continue

            # Constraint 1: There are two houses between Eric and Peter.
            pos_eric = name_perm.index("Eric") + 1
            pos_peter = name_perm.index("Peter") + 1
            if abs(pos_eric - pos_peter) != 3:
                continue

            # Constraint 4: There is one house between the person who is a doctor and Alice.
            pos_doctor = occ_perm.index("doctor") + 1
            pos_alice = alice_index + 1
            if abs(pos_doctor - pos_alice) != 2:
                continue

            # If all constraints are met, return the solution in order of houses
            solution = []
            for i in range(4):
                house_number = str(i + 1)
                solution.append([house_number, name_perm[i], occ_perm[i]])
            return solution
    return None

def main():
    solution_rows = solve_puzzle()
    output = {
        "solution": {
            "header": ["House", "Name", "Occupation"],
            "rows": solution_rows if solution_rows is not None else []
        }
    }
    print(json.dumps(output))

if __name__ == "__main__":
    main()