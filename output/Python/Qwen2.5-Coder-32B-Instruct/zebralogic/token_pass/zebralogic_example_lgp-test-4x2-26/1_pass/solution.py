import itertools
import json

# Define the names and occupations
names = ['Arnold', 'Eric', 'Peter', 'Alice']
occupations = ['doctor', 'engineer', 'artist', 'teacher']

# Generate all permutations of names and occupations
name_permutations = list(itertools.permutations(names))
occupation_permutations = list(itertools.permutations(occupations))

def is_valid_solution(name_perm, occ_perm):
    # Unpack the permutations
    (arnold_house, eric_house, peter_house, alice_house) = [names.index(name) + 1 for name in name_perm]
    (doctor_house, engineer_house, artist_house, teacher_house) = [occupations.index(occ) + 1 for occ in occ_perm]
    
    # Apply the constraints
    if abs(eric_house - peter_house) != 3:  # Two houses between Eric and Peter
        return False
    if teacher_house != peter_house:        # Peter is the teacher
        return False
    if peter_house == 1:                    # Peter is not in the first house
        return False
    if abs(doctor_house - alice_house) != 2: # One house between the doctor and Alice
        return False
    if artist_house != alice_house:         # Alice is the artist
        return False
    
    return True

# Find the valid solution
for name_perm in name_permutations:
    for occ_perm in occupation_permutations:
        if is_valid_solution(name_perm, occ_perm):
            solution = {
                "solution": {
                    "header": ["House", "Name", "Occupation"],
                    "rows": []
                }
            }
            for house in range(1, 5):
                name_index = name_perm.index(names[house-1])
                occupation = occ_perm[name_index]
                solution["solution"]["rows"].append([str(house), names[house-1], occupation])
            
            # Output the solution as JSON
            print(json.dumps(solution, indent=2))
            break
    else:
        continue
    break