import itertools
import json

names = ['Arnold', 'Peter', 'Carol', 'Alice', 'Bob', 'Eric']
children_base = ['Alice', 'Timothy', 'Bella', 'Fred', 'Samantha']
smoothie_base = ['desert', 'cherry', 'watermelon', 'blueberry', 'lime']

for name_perm in itertools.permutations(names):
    for child_first_five in itertools.permutations(children_base):
        child_perm = list(child_first_five) + ['Meredith']
        for smoothie_first_five in itertools.permutations(smoothie_base):
            smoothie_perm = list(smoothie_first_five) + ['dragonfruit']
            # Check if Alice's info is correct
            alice_index = None
            for i in range(6):
                if name_perm[i] == 'Alice':
                    if child_perm[i] == 'Alice' and smoothie_perm[i] == 'watermelon':
                        alice_index = i
                        break
            else:
                continue  # No valid Alice position
            # Check constraint 3: Alice not in fifth house (index 4)
            if alice_index == 4:
                continue
            # Check constraint 9: Arnold not in index 1
            arnold_index = name_perm.index('Arnold')
            if arnold_index == 1:
                continue
            # Check constraint 11: Arnold directly left of Carol
            carol_index = name_perm.index('Carol')
            if carol_index != arnold_index + 1:
                continue
            # Check constraint 10: Bob's child is Timothy
            bob_index = name_perm.index('Bob')
            if child_perm[bob_index] != 'Timothy':
                continue
            # Check constraint 12: Cherry directly left of Samantha
            try:
                cherry_index = smoothie_perm.index('cherry')
            except ValueError:
                continue
            samantha_index = child_perm.index('Samantha')
            if cherry_index + 1 != samantha_index:
                continue
            # Check constraint 4: Samantha not in index 1
            if samantha_index == 1:
                continue
            # Check constraint 8: Peter's index > samantha_index
            peter_index = name_perm.index('Peter')
            if peter_index <= samantha_index:
                continue
            # Check constraint 5: Watermelon (Alice's) is right of Cherry
            if alice_index <= cherry_index:
                continue
            # Check constraint 2: Blueberry left of Fred
            try:
                blueberry_index = smoothie_perm.index('blueberry')
            except ValueError:
                continue
            fred_index = child_perm.index('Fred')
            if blueberry_index >= fred_index:
                continue
            # Check constraint 1: Fred and Desert adjacent
            desert_index = smoothie_perm.index('desert')
            if abs(fred_index - desert_index) != 1:
                continue
            # All constraints passed. Build solution.
            solution_rows = []
            for i in range(6):
                house_num = i + 1
                solution_rows.append([
                    str(house_num),
                    name_perm[i],
                    child_perm[i],
                    smoothie_perm[i]
                ])
            solution = {
                "solution": {
                    "header": ["House", "Name", "Children", "Smoothie"],
                    "rows": solution_rows
                }
            }
            print(json.dumps(solution, indent=2))
            exit()