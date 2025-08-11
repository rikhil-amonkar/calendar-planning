#!/usr/bin/env python3
import json
from itertools import permutations

def solve():
    names = ["Bob", "Arnold", "Carol", "Alice", "Peter", "Eric"]
    genres = ["romance", "historical fiction", "biography", "mystery", "fantasy", "science fiction"]
    occupations = ["artist", "doctor", "nurse", "engineer", "teacher", "lawyer"]

    valid_solution = None

    # Iterate over possible name assignments for houses 1..6
    for perm_names in permutations(names):
        # Clue 12: Eric is in the third house (index 2)
        if perm_names[2] != "Eric":
            continue
        # Clue 5: Bob is not in the fifth house (index 4)
        if perm_names[4] == "Bob":
            continue
        # Get indices for key persons
        posAlice = perm_names.index("Alice")
        posCarol = perm_names.index("Carol")
        posBob = perm_names.index("Bob")
        posArnold = perm_names.index("Arnold")
        # Clue 13: The person who loves mystery (Carol) is not in the fifth house
        if posCarol == 4:
            continue

        # Iterate over possible occupations assignments
        for perm_occ in permutations(occupations):
            # Clue 10: The person who is a doctor is in the first house (index 0)
            if perm_occ[0] != "doctor":
                continue
            # Clue 4 & 1: Alice is the person who loves fantasy books and must be a lawyer.
            if perm_occ[posAlice] != "lawyer":
                continue
            # Clue 7: The person who is a nurse is directly left of Alice.
            if posAlice == 0 or perm_occ[posAlice - 1] != "nurse":
                continue
            # Clue 6: Arnold is somewhere to the left of the person who is an engineer.
            try:
                posEngineer = perm_occ.index("engineer")
            except ValueError:
                continue
            if posArnold >= posEngineer:
                continue

            # Iterate over possible book genre assignments
            for perm_gen in permutations(genres):
                # Clue 1: Alice loves fantasy books.
                if perm_gen[posAlice] != "fantasy":
                    continue
                # Clue 3: Carol is the person who loves mystery books.
                if perm_gen[posCarol] != "mystery":
                    continue

                # Now check cross-attribute and positional constraints across houses.
                valid = True
                teacher_index = None
                for i in range(6):
                    # Clue 8: The person who loves biography books is the person who is a teacher.
                    if perm_occ[i] == "teacher":
                        if perm_gen[i] != "biography":
                            valid = False
                            break
                        teacher_index = i
                    if perm_gen[i] == "biography" and perm_occ[i] != "teacher":
                        valid = False
                        break
                    # Clue 11: The person who loves science fiction books is the person who is an artist.
                    if perm_occ[i] == "artist" and perm_gen[i] != "science fiction":
                        valid = False
                        break
                    if perm_gen[i] == "science fiction" and perm_occ[i] != "artist":
                        valid = False
                        break
                    # Clue 4 (reiterated): The lawyer must love fantasy books.
                    if perm_occ[i] == "lawyer" and perm_gen[i] != "fantasy":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 9: The person who loves historical fiction is somewhere to the left of the person who is a teacher.
                if teacher_index is not None:
                    posHist = perm_gen.index("historical fiction")
                    if teacher_index <= posHist:
                        continue

                # Clue 2: The person who loves mystery books and Bob are next to each other.
                if abs(posCarol - posBob) != 1:
                    continue

                # All constraints satisfied, build the solution.
                solution = []
                for i in range(6):
                    solution.append([str(i+1), perm_names[i], perm_gen[i], perm_occ[i]])
                valid_solution = solution
                break
            if valid_solution is not None:
                break
        if valid_solution is not None:
            break

    return valid_solution

def main():
    solution = solve()
    result = {
        "solution": {
            "header": ["House", "Name", "book genre", "occupation"],
            "rows": solution
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()