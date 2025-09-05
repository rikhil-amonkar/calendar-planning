import json
import itertools

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Arnold", "Eric", "Peter", "Alice"]
    occupations = ["doctor", "engineer", "artist", "teacher"]

    # There are 4 houses, each with a unique name and occupation.
    # We'll represent a configuration by two lists of length 4:
    # name_assignment: a permutation of names for houses 1..4 (index 0->house1)
    # occ_assignment: a permutation of occupations for houses 1..4
    # We need to enforce constraints from the clues.
    
    for name_perm in itertools.permutations(names):
        # Constraint: Peter is not in the first house.
        if name_perm[0] == "Peter":
            continue

        # Constraint: There are two houses between Eric and Peter.
        # Find indices of Eric and Peter.
        eric_index = name_perm.index("Eric")
        peter_index = name_perm.index("Peter")
        if abs(eric_index - peter_index) != 3:
            continue

        for occ_perm in itertools.permutations(occupations):
            # Constraint: The person who is a teacher is Peter.
            # The house with teacher must have the person Peter.
            teacher_house = occ_perm.index("teacher")
            if name_perm[teacher_house] != "Peter":
                continue

            # Constraint: The person who is an artist is Alice.
            artist_house = occ_perm.index("artist")
            if name_perm[artist_house] != "Alice":
                continue

            # Constraint: There is one house between the person who is a doctor and Alice.
            # Find the index of the doctor and the index of Alice.
            doctor_house = occ_perm.index("doctor")
            alice_house = name_perm.index("Alice")
            if abs(doctor_house - alice_house) != 2:
                continue

            # If all constraints pass, return the solution.
            solution = []
            for i in range(4):
                # House numbers as strings.
                house_number = str(houses[i])
                solution.append([house_number, name_perm[i], occ_perm[i]])
            return {"solution": {"header": ["House", "Name", "Occupation"],
                                 "rows": solution}}
    return None

if __name__ == '__main__':
    result = solve_puzzle()
    print(json.dumps(result, indent=2))