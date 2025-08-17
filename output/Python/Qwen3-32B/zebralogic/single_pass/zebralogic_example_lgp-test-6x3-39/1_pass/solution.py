import itertools
import json

names = ['Arnold', 'Peter', 'Carol', 'Alice', 'Bob', 'Eric']
children_list = ['Alice', 'Timothy', 'Bella', 'Meredith', 'Fred', 'Samantha']
smoothie_list = ['desert', 'cherry', 'watermelon', 'blueberry', 'lime', 'dragonfruit']

valid_names = []
for p in itertools.permutations(names):
    # Check Arnold directly left of Carol
    found = False
    for i in range(5):
        if p[i] == 'Arnold' and p[i + 1] == 'Carol':
            found = True
            break
    if not found:
        continue
    # Check Arnold not in position 1 (house 2)
    if p[1] == 'Arnold':
        continue
    valid_names.append(p)

valid_children = []
for p in itertools.permutations(children_list):
    if p[5] == 'Meredith':  # house 6
        valid_children.append(p)

valid_smoothies = []
for p in itertools.permutations(smoothie_list):
    if p[5] == 'dragonfruit':  # house 6
        valid_smoothies.append(p)

for name_perm in valid_names:
    for children_perm in valid_children:
        for smoothie_perm in valid_smoothies:
            # Clue 1: Fred and desert adjacent
            fred_index = children_perm.index('Fred')
            desert_adjacent = False
            if fred_index > 0 and smoothie_perm[fred_index - 1] == 'desert':
                desert_adjacent = True
            if fred_index < 5 and smoothie_perm[fred_index + 1] == 'desert':
                desert_adjacent = True
            if not desert_adjacent:
                continue

            # Clue 2: Blueberry left of Fred
            blueberry_index = smoothie_perm.index('blueberry')
            if blueberry_index >= fred_index:
                continue

            # Clue 3: Alice not in fifth house (index 4)
            if name_perm[4] == 'Alice':
                continue

            # Clue 4: children_perm[1] != 'Samantha'
            if children_perm[1] == 'Samantha':
                continue

            # Clue 5: Watermelon right of Cherry
            try:
                watermelon_index = smoothie_perm.index('watermelon')
                cherry_index = smoothie_perm.index('cherry')
            except ValueError:
                continue
            if watermelon_index <= cherry_index:
                continue

            # Clue 6: Alice's child is Alice
            alice_name_index = name_perm.index('Alice')
            if children_perm[alice_name_index] != 'Alice':
                continue

            # Clue 7: Alice's smoothie is watermelon
            if smoothie_perm[alice_name_index] != 'watermelon':
                continue

            # Clue 8: Peter to the right of Samantha's child
            samantha_index = children_perm.index('Samantha')
            peter_index = name_perm.index('Peter')
            if peter_index <= samantha_index:
                continue

            # Clue 10: Bob's child is Timothy
            bob_index = name_perm.index('Bob')
            if children_perm[bob_index] != 'Timothy':
                continue

            # Clue 12: Cherry directly left of Samantha
            cherry_index = smoothie_perm.index('cherry')
            if cherry_index + 1 >= 6 or children_perm[cherry_index + 1] != 'Samantha':
                continue

            # All constraints passed
            solution_rows = []
            for i in range(6):
                house_num = i + 1
                solution_rows.append([str(house_num), name_perm[i], children_perm[i], smoothie_perm[i]])

            solution = {
                "solution": {
                    "header": ["House", "Name", "Children", "Smoothie"],
                    "rows": solution_rows
                }
            }

            print(json.dumps(solution))
            exit()

# If no solution found
print(json.dumps({"solution": {"header": [], "rows": []}}))