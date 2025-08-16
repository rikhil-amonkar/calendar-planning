import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ['Arnold', 'Eric', 'Peter', 'Alice']
    occupations = ['doctor', 'engineer', 'artist', 'teacher']

    # Generate all possible permutations for names and occupations
    for name_perm in permutations(names):
        for occ_perm in permutations(occupations):
            solution = {}
            valid = True

            # Assign names and occupations to houses
            for i in range(4):
                solution[i+1] = {
                    'Name': name_perm[i],
                    'Occupation': occ_perm[i]
                }

            # Check constraints
            # Constraint 1: Two houses between Eric and Peter
            eric_pos = None
            peter_pos = None
            for house in solution:
                if solution[house]['Name'] == 'Eric':
                    eric_pos = house
                if solution[house]['Name'] == 'Peter':
                    peter_pos = house
            if eric_pos is None or peter_pos is None or abs(eric_pos - peter_pos) != 3:
                valid = False
                continue

            # Constraint 2: Teacher is Peter
            for house in solution:
                if solution[house]['Name'] == 'Peter' and solution[house]['Occupation'] != 'teacher':
                    valid = False
                    break
            if not valid:
                continue

            # Constraint 3: Peter not in first house
            if solution[1]['Name'] == 'Peter':
                valid = False
                continue

            # Constraint 4: One house between doctor and Alice
            doctor_pos = None
            alice_pos = None
            for house in solution:
                if solution[house]['Occupation'] == 'doctor':
                    doctor_pos = house
                if solution[house]['Name'] == 'Alice':
                    alice_pos = house
            if doctor_pos is None or alice_pos is None or abs(doctor_pos - alice_pos) != 2:
                valid = False
                continue

            # Constraint 5: Artist is Alice
            for house in solution:
                if solution[house]['Name'] == 'Alice' and solution[house]['Occupation'] != 'artist':
                    valid = False
                    break
            if not valid:
                continue

            # If all constraints are satisfied, format the solution
            if valid:
                result = {
                    "solution": {
                        "header": ["House", "Name", "Occupation"],
                        "rows": []
                    }
                }
                for house in sorted(solution.keys()):
                    row = [str(house), solution[house]['Name'], solution[house]['Occupation']]
                    result["solution"]["rows"].append(row)
                return json.dumps(result, indent=2)

    return json.dumps({"solution": {"header": ["House", "Name", "Occupation"], "rows": []}})

print(solve_puzzle())