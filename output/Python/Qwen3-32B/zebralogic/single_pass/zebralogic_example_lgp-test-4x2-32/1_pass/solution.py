import itertools
import json

names = ['Peter', 'Arnold', 'Eric', 'Alice']
pets = ['bird', 'fish', 'dog', 'cat']

for name_perm in itertools.permutations(names):
    # Check clue 2: Eric is not in first house
    if name_perm[0] == 'Eric':
        continue
    # Check clue 5: Alice is not in first house
    if name_perm[0] == 'Alice':
        continue

    # Find Arnold's and Eric's positions
    arnold_idx = name_perm.index('Arnold')
    eric_idx = name_perm.index('Eric')

    # Initialize pet list
    pet = [None] * 4
    pet[arnold_idx] = 'fish'  # Clue 6
    pet[eric_idx] = 'bird'    # Clue 3

    # Remaining pet indices
    remaining_pet_indices = [i for i in range(4) if pet[i] is None]
    remaining_pet_values = ['dog', 'cat']

    # Try all permutations for remaining pets
    for pet_perm in itertools.permutations(remaining_pet_values):
        temp_pet = pet.copy()
        for i, val in zip(remaining_pet_indices, pet_perm):
            temp_pet[i] = val

        # Check clue 4: one house between fish (Arnold) and Peter
        peter_idx = name_perm.index('Peter')
        arnold_house = arnold_idx + 1  # house number
        peter_house = peter_idx + 1
        if abs(peter_house - arnold_house) != 2:
            continue

        # Check clue 1: dog is to the right of Alice
        alice_idx = name_perm.index('Alice')
        dog_idx = temp_pet.index('dog')
        if dog_idx <= alice_idx:
            continue

        # If all constraints are satisfied, build the solution
        solution_rows = []
        for house_num in range(1, 5):
            idx = house_num - 1
            solution_rows.append([
                str(house_num),
                name_perm[idx],
                temp_pet[idx]
            ])

        solution = {
            "solution": {
                "header": ["House", "Name", "Pet"],
                "rows": solution_rows
            }
        }

        # Output as JSON
        print(json.dumps(solution))
        exit()

# If no solution found (though there should be one)
print(json.dumps({"solution": {"header": [], "rows": []}}))