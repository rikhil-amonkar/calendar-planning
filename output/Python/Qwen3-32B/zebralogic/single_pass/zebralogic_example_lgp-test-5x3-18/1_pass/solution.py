from itertools import permutations
import json

names = ['Alice', 'Eric', 'Arnold', 'Bob', 'Peter']
flowers = ['tulips', 'roses', 'lilies', 'daffodils', 'carnations']
animals = ['dog', 'horse', 'cat', 'bird', 'fish']

for name_perm in permutations(names):
    if name_perm[1] != 'Alice':
        continue  # Clue 1
    for flower_perm in permutations(flowers):
        for animal_perm in permutations(animals):
            # Clue 2: lilies → bird
            lilies_index = flower_perm.index('lilies')
            if animal_perm[lilies_index] != 'bird':
                continue
            # Clue 4: fish → daffodils
            fish_index = animal_perm.index('fish')
            if flower_perm[fish_index] != 'daffodils':
                continue
            # Clue 5: Eric → horse
            eric_index = name_perm.index('Eric')
            if animal_perm[eric_index] != 'horse':
                continue
            # Clue 7: fish directly left of Bob
            fish_i = animal_perm.index('fish')
            if fish_i + 1 >= len(name_perm) or name_perm[fish_i + 1] != 'Bob':
                continue
            # Clue 8: Alice directly left of horse (house 3)
            if animal_perm[2] != 'horse':
                continue
            # Clue 9: carnations directly left of tulips
            try:
                carnations_i = flower_perm.index('carnations')
                if carnations_i + 1 >= len(flower_perm) or flower_perm[carnations_i + 1] != 'tulips':
                    continue
            except ValueError:
                continue
            # Clue 3: Peter to the right of tulips
            tulips_i = flower_perm.index('tulips')
            peter_i = name_perm.index('Peter')
            if peter_i <= tulips_i:
                continue
            # Clue 6: two houses between dog and Bob
            dog_i = animal_perm.index('dog')
            bob_i = name_perm.index('Bob')
            if abs(dog_i - bob_i) != 3:
                continue
            # Clue 10: cat not in first house
            cat_i = animal_perm.index('cat')
            if cat_i == 0:
                continue
            # Construct solution
            solution_rows = []
            for i in range(5):
                house_num = i + 1
                solution_rows.append([str(house_num), name_perm[i], flower_perm[i], animal_perm[i]])
            solution = {
                "solution": {
                    "header": ["House", "Name", "Flower", "Animal"],
                    "rows": solution_rows
                }
            }
            print(json.dumps(solution))
            exit()