import itertools
import json

def solve_puzzle():
    # Define the attributes
    houses = [1, 2, 3, 4]
    names = ['Arnold', 'Eric', 'Peter', 'Alice']
    occupations = ['doctor', 'engineer', 'artist', 'teacher']
    
    # Generate all possible permutations of names and occupations
    for name_perm in itertools.permutations(names):
        for occ_perm in itertools.permutations(occupations):
            # Assign names and occupations to houses
            assignment = []
            for i in range(4):
                assignment.append({
                    'House': str(i + 1),
                    'Name': name_perm[i],
                    'Occupation': occ_perm[i]
                })
            
            # Check all constraints
            # Constraint 1: Two houses between Eric and Peter
            eric_pos = None
            peter_pos = None
            for house in assignment:
                if house['Name'] == 'Eric':
                    eric_pos = int(house['House'])
                if house['Name'] == 'Peter':
                    peter_pos = int(house['House'])
            if eric_pos is None or peter_pos is None:
                continue
            if abs(eric_pos - peter_pos) != 3:
                continue
            
            # Constraint 2: The teacher is Peter
            for house in assignment:
                if house['Name'] == 'Peter' and house['Occupation'] != 'teacher':
                    break
            else:
                # Constraint 3: Peter is not in the first house
                if peter_pos == 1:
                    continue
                
                # Constraint 4: One house between doctor and Alice
                doctor_pos = None
                alice_pos = None
                for house in assignment:
                    if house['Occupation'] == 'doctor':
                        doctor_pos = int(house['House'])
                    if house['Name'] == 'Alice':
                        alice_pos = int(house['House'])
                if doctor_pos is None or alice_pos is None:
                    continue
                if abs(doctor_pos - alice_pos) != 2:
                    continue
                
                # Constraint 5: The artist is Alice
                for house in assignment:
                    if house['Name'] == 'Alice' and house['Occupation'] != 'artist':
                        break
                else:
                    # All constraints satisfied
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Occupation"],
                            "rows": []
                        }
                    }
                    for house in assignment:
                        solution["solution"]["rows"].append([
                            house['House'],
                            house['Name'],
                            house['Occupation']
                        ])
                    return json.dumps(solution, indent=2)
    
    return json.dumps({"solution": {}})

print(solve_puzzle())