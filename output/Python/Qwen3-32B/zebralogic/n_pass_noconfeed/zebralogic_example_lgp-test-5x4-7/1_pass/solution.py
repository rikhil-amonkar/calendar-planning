import itertools
import json

def solve_puzzle():
    # Define the options for each category
    animal_options = ['horse', 'dog', 'bird', 'fish', 'cat']
    nationality_options = ['german', 'swede', 'norwegian', 'brit', 'dane']
    name_options = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    smoothie_options = ['lime', 'dragonfruit', 'desert', 'watermelon', 'cherry']

    # Generate all possible animal permutations with 'horse' in the third house (index 2)
    animal_perms = [p for p in itertools.permutations(animal_options) if p[2] == 'horse']

    # Generate all possible nationality permutations with 'dane' in the third house (index 2)
    nationality_perms = [p for p in itertools.permutations(nationality_options) if p[2] == 'dane']

    # Generate all possible name and smoothie permutations
    name_perms = list(itertools.permutations(name_options))
    smoothie_perms = list(itertools.permutations(smoothie_options))

    # Iterate through all possible combinations
    for animal in animal_perms:
        for nationality in nationality_perms:
            for names in name_perms:
                for smoothie in smoothie_perms:
                    # Check clue 12: Norwegian is Alice
                    norwegian_index = nationality.index('norwegian')
                    if names[norwegian_index] != 'Alice':
                        continue

                    # Check clue 4: bird is after cat
                    try:
                        cat_index = animal.index('cat')
                        bird_index = animal.index('bird')
                    except ValueError:
                        continue
                    if bird_index <= cat_index:
                        continue

                    # Check clue 6: name at cat index is Eric
                    if names[cat_index] != 'Eric':
                        continue

                    # Check clue 7: name at bird index is Bob
                    if names[bird_index] != 'Bob':
                        continue

                    # Check clue 9: smoothie at bird index is watermelon
                    if smoothie[bird_index] != 'watermelon':
                        continue

                    # Check clue 10: for all i, if smoothie[i] is desert, then animal[i] is dog
                    valid_clue10 = True
                    for i in range(5):
                        if smoothie[i] == 'desert' and animal[i] != 'dog':
                            valid_clue10 = False
                            break
                    if not valid_clue10:
                        continue

                    # Check clue 5: for all dog positions, next smoothie is lime
                    dog_positions = [i for i in range(5) if animal[i] == 'dog']
                    valid_clue5 = True
                    for i in dog_positions:
                        if i + 1 >= 5 or smoothie[i + 1] != 'lime':
                            valid_clue5 = False
                            break
                    if not valid_clue5:
                        continue

                    # Check clue 1: for all swede positions, next animal is dog
                    swede_positions = [i for i in range(5) if nationality[i] == 'swede']
                    valid_clue1 = True
                    for i in swede_positions:
                        if i + 1 >= 5 or animal[i + 1] != 'dog':
                            valid_clue1 = False
                            break
                    if not valid_clue1:
                        continue

                    # Check clue 2: dog and Brit positions have difference of 3
                    try:
                        dog_i = animal.index('dog')
                        brit_i = nationality.index('brit')
                    except ValueError:
                        continue
                    if abs(dog_i - brit_i) != 3:
                        continue

                    # Check clue 8: for all cherry positions, next name is Peter
                    cherry_positions = [i for i in range(5) if smoothie[i] == 'cherry']
                    valid_clue8 = True
                    for i in cherry_positions:
                        if i + 1 >= 5 or names[i + 1] != 'Peter':
                            valid_clue8 = False
                            break
                    if not valid_clue8:
                        continue

                    # If all checks passed, construct the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
                            "rows": []
                        }
                    }
                    for i in range(5):
                        house_num = str(i + 1)
                        name_val = names[i]
                        smoothie_val = smoothie[i]
                        animal_val = animal[i]
                        nationality_val = nationality[i]
                        solution["solution"]["rows"].append([
                            house_num, name_val, smoothie_val, animal_val, nationality_val
                        ])

                    # Output the JSON
                    print(json.dumps(solution))
                    return

solve_puzzle()