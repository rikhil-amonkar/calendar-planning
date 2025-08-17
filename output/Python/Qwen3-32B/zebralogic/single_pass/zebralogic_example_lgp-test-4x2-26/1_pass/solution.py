import itertools
import json

# Define the possible names and occupations
names = ['Arnold', 'Eric', 'Peter', 'Alice']
occupations = ['doctor', 'engineer', 'artist', 'teacher']

solution = None

# Iterate through all possible permutations of names and occupations
for name_perm in itertools.permutations(names):
    # Check clue 1: two houses between Eric and Peter
    eric_pos = name_perm.index('Eric')
    peter_pos = name_perm.index('Peter')
    if abs(eric_pos - peter_pos) != 3:
        continue
    # Check clue 3: Peter is not in the first house (index 0)
    if peter_pos == 0:
        continue
    
    # Find Alice's position
    alice_pos = name_perm.index('Alice')
    
    # Check all occupation permutations
    for occ_perm in itertools.permutations(occupations):
        # Check clue 2: Peter is the teacher
        if occ_perm[peter_pos] != 'teacher':
            continue
        # Check clue 5: Alice is the artist
        if occ_perm[alice_pos] != 'artist':
            continue
        # Check clue 4: one house between doctor and Alice
        doctor_pos = occ_perm.index('doctor')
        if abs(doctor_pos - alice_pos) != 2:
            continue
        
        # If we reach here, we have a valid solution
        rows = []
        for i in range(4):
            house = str(i + 1)
            name = name_perm[i]
            occ = occ_perm[i]
            rows.append([house, name, occ])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation"],
                "rows": rows
            }
        }
        # Break out of loops
        break
    if solution:
        break

# Output the solution as JSON
print(json.dumps(solution))