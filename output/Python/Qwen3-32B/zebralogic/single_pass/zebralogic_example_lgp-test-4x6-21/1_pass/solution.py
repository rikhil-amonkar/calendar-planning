import itertools
import json

# Define the possible values for each category
possible_names = ['Peter', 'Arnold', 'Alice', 'Eric']
possible_styles = ['craftsman', 'colonial', 'ranch', 'victorian']
possible_flowers = ['roses', 'daffodils', 'carnations', 'lilies']
possible_hobbies = ['photography', 'painting', 'cooking', 'gardening']
possible_pets = ['dog', 'fish', 'bird', 'cat']

# Mapping of flowers to colors based on clues
flower_to_color = {
    'roses': 'red',
    'daffodils': 'yellow',
    'carnations': 'white',
    'lilies': 'green'
}

# Iterate through all permutations for names
for name_perm in itertools.permutations(possible_names):
    # Clue 1 and 6: Arnold is in house 2 (index 1)
    if name_perm[1] != 'Arnold':
        continue

    # Iterate through all permutations for house styles
    for style_perm in itertools.permutations(possible_styles):
        # Clue 6: Craftsman is in house 2 (index 1)
        if style_perm[1] != 'craftsman':
            continue

        # Clue 7: Eric's house is Victorian
        eric_index = name_perm.index('Eric')
        if style_perm[eric_index] != 'victorian':
            continue

        # Iterate through all permutations for flowers
        for flower_perm in itertools.permutations(possible_flowers):
            # Derive color permutation from flower permutation
            color_perm = [flower_to_color[flower] for flower in flower_perm]

            # Clue 4: Daffodils are not in house 4 (index 3)
            if flower_perm[3] == 'daffodils':
                continue

            # Clue 13: Colonial-style house has red color
            colonial_index = style_perm.index('colonial')
            if color_perm[colonial_index] != 'red':
                continue

            # Clue 5: Roses lover has red color
            roses_index = flower_perm.index('roses')
            if color_perm[roses_index] != 'red':
                continue

            # Clue 12: Daffodils lover has yellow color
            daffodils_index = flower_perm.index('daffodils')
            if color_perm[daffodils_index] != 'yellow':
                continue

            # Iterate through all permutations for pets
            for pet_perm in itertools.permutations(possible_pets):
                # Clue 14: Eric has cat
                if pet_perm[eric_index] != 'cat':
                    continue

                # Check Clue 8 and 10: White color must have fish pet
                valid_white = True
                for i in range(4):
                    if color_perm[i] == 'white' and pet_perm[i] != 'fish':
                        valid_white = False
                        break
                if not valid_white:
                    continue

                # Iterate through all permutations for hobbies
                for hobby_perm in itertools.permutations(possible_hobbies):
                    # Clue 3: Photography hobby must have dog pet
                    valid_photography = True
                    for i in range(4):
                        if hobby_perm[i] == 'photography' and pet_perm[i] != 'dog':
                            valid_photography = False
                            break
                    if not valid_photography:
                        continue

                    # Clue 9: Cooking is to the right of red color
                    cooking_index = hobby_perm.index('cooking')
                    red_index = color_perm.index('red')
                    if cooking_index <= red_index:
                        continue

                    # Clue 11: White color is to the right of gardening hobby
                    white_index = color_perm.index('white')
                    gardening_index = hobby_perm.index('gardening')
                    if white_index <= gardening_index:
                        continue

                    # Clue 2: Roses lover is to the right of Peter
                    peter_index = name_perm.index('Peter')
                    if roses_index <= peter_index:
                        continue

                    # If all constraints are satisfied, construct the solution
                    solution = []
                    for i in range(4):
                        house_num = i + 1
                        solution.append([
                            str(house_num),
                            name_perm[i],
                            flower_perm[i],
                            hobby_perm[i],
                            pet_perm[i],
                            color_perm[i],
                            style_perm[i]
                        ])

                    # Output the solution in the required JSON format
                    print(json.dumps({
                        "solution": {
                            "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
                            "rows": solution
                        }
                    }))
                    exit()