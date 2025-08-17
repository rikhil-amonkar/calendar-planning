import itertools
import json
import sys

names = ['Eric', 'Peter', 'Arnold']
mothers = ['Holly', 'Aniya', 'Janelle']
foods = ['pizza', 'grilled cheese', 'spaghetti']

for name_perm in itertools.permutations(names):
    for mother_perm in itertools.permutations(mothers):
        for food_perm in itertools.permutations(foods):
            # Check Clue 3: The person who loves grilled cheese is Eric
            gc_index = food_perm.index('grilled cheese')
            if name_perm[gc_index] != 'Eric':
                continue

            # Check Clue 4: Peter's mother is Holly
            peter_index = name_perm.index('Peter')
            if mother_perm[peter_index] != 'Holly':
                continue

            # Check Clue 2: Grilled cheese lover is directly left of mother Aniya
            if gc_index + 1 >= 3 or mother_perm[gc_index + 1] != 'Aniya':
                continue

            # Check Clue 1: Spaghetti eater and Peter are next to each other
            spaghetti_index = food_perm.index('spaghetti')
            if abs(spaghetti_index - peter_index) != 1:
                continue

            # Build solution
            rows = []
            for i in range(3):
                house = str(i + 1)
                name = name_perm[i]
                mother = mother_perm[i]
                food = food_perm[i]
                rows.append([house, name, mother, food])

            solution = {
                "solution": {
                    "header": ["House", "Name", "Mother", "Food"],
                    "rows": rows
                }
            }

            print(json.dumps(solution))
            sys.exit()