import itertools
import json

names = ['Arnold', 'Bob', 'Alice', 'Eric', 'Peter']
heights = ['very tall', 'average', 'tall', 'very short', 'short']
foods = ['stew', 'grilled cheese', 'spaghetti', 'pizza', 'stir fry']

for name_perm in itertools.permutations(names):
    for height_perm in itertools.permutations(heights):
        if height_perm[2] != 'tall':
            continue
        if name_perm[2] != 'Eric':
            continue
        for food_perm in itertools.permutations(foods):
            if food_perm[2] != 'pizza':
                continue

            # Clue 1: Alice is short
            alice_idx = name_perm.index('Alice')
            if height_perm[alice_idx] != 'short':
                continue

            # Clue 3: average not in second house
            if height_perm[1] == 'average':
                continue

            # Clue 5: Arnold's food is stir fry
            arnold_idx = name_perm.index('Arnold')
            if food_perm[arnold_idx] != 'stir fry':
                continue

            # Clue 4: average left of stew
            avg_idx = height_perm.index('average')
            stew_idx = food_perm.index('stew')
            if avg_idx >= stew_idx:
                continue

            # Clue 8: Bob right of Arnold
            bob_idx = name_perm.index('Bob')
            arnold_idx = name_perm.index('Arnold')
            if arnold_idx >= bob_idx:
                continue

            # Clue 9: grilled cheese right of Eric (house 3)
            gc_idx = food_perm.index('grilled cheese')
            if gc_idx <= 2:
                continue

            # Clue 10: very short left of Arnold
            vshort_idx = height_perm.index('very short')
            arnold_idx = name_perm.index('Arnold')
            if vshort_idx >= arnold_idx:
                continue

            # Build solution
            rows = []
            for i in range(5):
                house = str(i + 1)
                name = name_perm[i]
                height = height_perm[i]
                food = food_perm[i]
                rows.append([house, name, height, food])

            solution = {
                "solution": {
                    "header": ["House", "Name", "Height", "Food"],
                    "rows": rows
                }
            }

            print(json.dumps(solution))
            exit()

# Fallback if no solution found
print(json.dumps({"solution": {"header": [], "rows": []}}))