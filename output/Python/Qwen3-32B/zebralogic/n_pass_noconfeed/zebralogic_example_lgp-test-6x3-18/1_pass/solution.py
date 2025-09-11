import itertools
import json

names = ['Arnold', 'Eric', 'Bob', 'Alice', 'Carol', 'Peter']
mothers = ['Sarah', 'Holly', 'Janelle', 'Aniya', 'Penny', 'Kailyn']
pets = ['hamster', 'dog', 'bird', 'cat', 'fish', 'rabbit']

solution_found = False

for names_p in itertools.permutations(names):
    # Clue 1: Bob is not in the second house.
    if names_p[1] == 'Bob':
        continue
    # Clue 8: Alice is directly left of Carol.
    i_alice = names_p.index('Alice')
    i_carol = names_p.index('Carol')
    if i_carol != i_alice + 1:
        continue

    for mothers_p in itertools.permutations(mothers):
        # Clue 9: Carol's mother is Aniya.
        if mothers_p[i_carol] != 'Aniya':
            continue

        for pets_p in itertools.permutations(pets):
            # Find indices for all pets
            i_rabbit = pets_p.index('rabbit')
            i_cat = pets_p.index('cat')
            i_hamster = pets_p.index('hamster')
            i_dog = pets_p.index('dog')
            i_fish = pets_p.index('fish')

            # Clue 12: Fish owner's mother is Sarah.
            if mothers_p[i_fish] != 'Sarah':
                continue

            # Clue 5: Rabbit owner is Eric.
            if names_p[i_rabbit] != 'Eric':
                continue

            # Clue 11: Rabbit's mother is Kailyn.
            if mothers_p[i_rabbit] != 'Kailyn':
                continue

            # Clue 10: Arnold has the cat.
            if names_p[i_cat] != 'Arnold':
                continue

            # Clue 7: Cat's mother is Janelle.
            if mothers_p[i_cat] != 'Janelle':
                continue

            # Clue 3: Cat is directly left of Holly's mother.
            if i_cat + 1 >= 6 or mothers_p[i_cat + 1] != 'Holly':
                continue

            # Clue 2: Two houses between cat and rabbit.
            if abs(i_cat - i_rabbit) != 3:
                continue

            # Clue 4: Hamster is directly left of rabbit.
            if i_hamster + 1 != i_rabbit:
                continue

            # Clue 6: One house between dog and cat.
            if abs(i_dog - i_cat) != 2:
                continue

            # All constraints satisfied, build the solution
            rows = []
            for house_num in range(6):
                house = str(house_num + 1)
                name = names_p[house_num]
                mother = mothers_p[house_num]
                pet = pets_p[house_num]
                rows.append([house, name, mother, pet])

            solution = {
                "solution": {
                    "header": ["House", "Name", "Mother", "Pet"],
                    "rows": rows
                }
            }

            print(json.dumps(solution))
            solution_found = True
            break
        if solution_found:
            break
    if solution_found:
        break