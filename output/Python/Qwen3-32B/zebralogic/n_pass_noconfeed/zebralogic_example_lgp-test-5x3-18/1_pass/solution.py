import itertools
import json

names_list = ['Alice', 'Eric', 'Arnold', 'Bob', 'Peter']
flowers_list = ['tulips', 'roses', 'lilies', 'daffodils', 'carnations']
animals_list = ['dog', 'horse', 'cat', 'bird', 'fish']

for names in itertools.permutations(names_list):
    if names[1] != 'Alice':
        continue

    for animals in itertools.permutations(animals_list):
        if animals[2] != 'horse' or names[2] != 'Eric':
            continue

        for flowers in itertools.permutations(flowers_list):
            # Clue 2: lilies -> bird
            lilies_index = flowers.index('lilies')
            if animals[lilies_index] != 'bird':
                continue

            # Clue 4: fish -> daffodils
            fish_index = animals.index('fish')
            if flowers[fish_index] != 'daffodils':
                continue

            # Clue 7: fish directly left of Bob
            if fish_index + 1 >= 5 or names[fish_index + 1] != 'Bob':
                continue

            # Clue 3: Peter to the right of tulips lover
            tulips_index = flowers.index('tulips')
            peter_index = names.index('Peter')
            if peter_index <= tulips_index:
                continue

            # Clue 6: two houses between dog and Bob
            dog_index = animals.index('dog')
            bob_index = names.index('Bob')
            if abs(dog_index - bob_index) != 3:
                continue

            # Clue 9: carnations directly left of tulips
            carnations_index = flowers.index('carnations')
            if carnations_index + 1 >= 5 or flowers[carnations_index + 1] != 'tulips':
                continue

            # Clue 10: cat not in first house
            cat_index = animals.index('cat')
            if cat_index == 0:
                continue

            # Construct the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Flower", "Animal"],
                    "rows": []
                }
            }
            for i in range(5):
                house_num = str(i + 1)
                name = names[i]
                flower = flowers[i]
                animal = animals[i]
                solution["solution"]["rows"].append([house_num, name, flower, animal])

            print(json.dumps(solution))
            exit()