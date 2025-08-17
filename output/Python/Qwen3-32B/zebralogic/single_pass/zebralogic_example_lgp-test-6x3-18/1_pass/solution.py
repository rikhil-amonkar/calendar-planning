import itertools
import json

names = ['Arnold', 'Eric', 'Bob', 'Alice', 'Carol', 'Peter']
mothers = ['Sarah', 'Holly', 'Janelle', 'Aniya', 'Penny', 'Kailyn']
pets = ['hamster', 'dog', 'bird', 'cat', 'fish', 'rabbit']

solution_found = None

for name_perm in itertools.permutations(names):
    # Clue 1: Bob is not in the second house
    if name_perm[1] == 'Bob':
        continue

    # Check for Alice directly left of Carol (Clue 8)
    alice_carol = False
    carol_index = -1
    for i in range(5):
        if name_perm[i] == 'Alice' and name_perm[i+1] == 'Carol':
            alice_carol = True
            carol_index = i + 1
            break
    if not alice_carol:
        continue

    for mother_perm in itertools.permutations(mothers):
        # Clue 9: Carol's mother is Aniya
        if mother_perm[carol_index] != 'Aniya':
            continue

        # Clue 7: Arnold's mother is Janelle
        arnold_index = name_perm.index('Arnold')
        if mother_perm[arnold_index] != 'Janelle':
            continue

        for pet_perm in itertools.permutations(pets):
            # Clue 10: Arnold has cat
            if pet_perm[arnold_index] != 'cat':
                continue

            # Clue 5: Rabbit owner is Eric
            rabbit_index = pet_perm.index('rabbit')
            if name_perm[rabbit_index] != 'Eric':
                continue

            # Clue 11: Rabbit's mother is Kailyn
            if mother_perm[rabbit_index] != 'Kailyn':
                continue

            # Clue 12: Fish owner's mother is Sarah
            fish_index = pet_perm.index('fish')
            if mother_perm[fish_index] != 'Sarah':
                continue

            # Clue 3: Cat is directly left of Holly's mother
            cat_index = arnold_index
            if cat_index + 1 >= 6 or mother_perm[cat_index + 1] != 'Holly':
                continue

            # Clue 2: Two houses between cat and rabbit
            if abs(cat_index - rabbit_index) != 3:
                continue

            # Clue 4: Hamster directly left of rabbit
            hamster_index = rabbit_index - 1
            if hamster_index < 0 or hamster_index >= 6 or pet_perm[hamster_index] != 'hamster':
                continue

            # Clue 6: One house between dog and cat
            dog_index = pet_perm.index('dog')
            if abs(dog_index - cat_index) != 2:
                continue

            # If all constraints are satisfied
            solution_rows = []
            for i in range(6):
                house_num = str(i + 1)
                solution_rows.append([house_num, name_perm[i], mother_perm[i], pet_perm[i]])
            solution_found = {
                "solution": {
                    "header": ["House", "Name", "Mother", "Pet"],
                    "rows": solution_rows
                }
            }
            # Break out of loops
            break
        if solution_found:
            break
    if solution_found:
        break

print(json.dumps(solution_found))