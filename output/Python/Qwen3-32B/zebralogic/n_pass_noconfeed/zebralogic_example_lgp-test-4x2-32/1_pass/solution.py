import itertools
import json

# Define the possible names and pets
names = ['Peter', 'Arnold', 'Eric', 'Alice']
pets = ['bird', 'fish', 'dog', 'cat']

# Iterate through all permutations of names and pets
for name_perm in itertools.permutations(names):
    # Check if Eric is not in the first house
    if name_perm[0] == 'Eric':
        continue
    # Check if Alice is not in the first house
    if name_perm[0] == 'Alice':
        continue

    for pet_perm in itertools.permutations(pets):
        # Check if Arnold has fish and Eric has bird
        arnold_pos = name_perm.index('Arnold')
        if pet_perm[arnold_pos] != 'fish':
            continue
        eric_pos = name_perm.index('Eric')
        if pet_perm[eric_pos] != 'bird':
            continue

        # Check if the dog is to the right of Alice
        alice_pos = name_perm.index('Alice')
        dog_pos = pet_perm.index('dog')
        if alice_pos >= dog_pos:
            continue

        # Check if there is one house between fish (Arnold's house) and Peter
        fish_pos = arnold_pos
        peter_pos = name_perm.index('Peter')
        if abs(fish_pos - peter_pos) != 2:
            continue

        # If all constraints are satisfied, build the solution
        rows = []
        for i in range(4):
            house = str(i + 1)
            name = name_perm[i]
            pet = pet_perm[i]
            rows.append([house, name, pet])

        solution = {
            "solution": {
                "header": ["House", "Name", "Pet"],
                "rows": rows
            }
        }

        # Output the solution as JSON
        print(json.dumps(solution))
        exit()

# If no solution is found (though the puzzle should have one), output an empty structure
print(json.dumps({"solution": {"header": ["House", "Name", "Pet"], "rows": []}}))