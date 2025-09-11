import itertools
import json

# Define the possible names and occupations
names = ['Arnold', 'Eric', 'Peter', 'Alice']
occupations = ['doctor', 'engineer', 'artist', 'teacher']

# Iterate through all possible permutations of names
for name_perm in itertools.permutations(names):
    # Check clue 1 and 3: Eric and Peter have two houses between them, and Peter is not in the first house
    eric_house = None
    peter_house = None
    for i in range(4):
        if name_perm[i] == 'Eric':
            eric_house = i + 1  # Convert to 1-based house number
        if name_perm[i] == 'Peter':
            peter_house = i + 1
    if abs(eric_house - peter_house) != 3 or peter_house == 1:
        continue  # Skip invalid name permutations

    # Check occupation permutations
    for occ_perm in itertools.permutations(occupations):
        # Check clue 2: Peter is the teacher
        peter_index = name_perm.index('Peter')
        if occ_perm[peter_index] != 'teacher':
            continue

        # Check clue 5: Alice is the artist
        alice_index = name_perm.index('Alice')
        if occ_perm[alice_index] != 'artist':
            continue

        # Check clue 4: One house between the doctor and Alice
        doctor_house = None
        for i in range(4):
            if occ_perm[i] == 'doctor':
                doctor_house = i + 1  # Convert to 1-based house number
                break
        alice_house = alice_index + 1
        if abs(doctor_house - alice_house) != 2:
            continue

        # Construct the solution
        solution_rows = []
        for house_num in range(1, 5):
            idx = house_num - 1
            solution_rows.append([str(house_num), name_perm[idx], occ_perm[idx]])

        # Output as JSON
        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation"],
                "rows": solution_rows
            }
        }
        print(json.dumps(solution, indent=2))
        exit()  # Exit after finding the first valid solution

# Fallback in case no solution is found (should not happen)
print(json.dumps({"solution": {"header": ["House", "Name", "Occupation"], "rows": []}}))