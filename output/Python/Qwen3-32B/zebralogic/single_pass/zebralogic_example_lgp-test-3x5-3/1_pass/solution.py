import itertools
import json

# Define the possible values for each category
names = ['Eric', 'Peter', 'Arnold']
smoothies = ['cherry', 'watermelon', 'desert']
flowers = ['carnations', 'lilies', 'daffodils']
animals = ['cat', 'horse', 'bird']
hobbies = ['photography', 'cooking', 'gardening']

# Generate all permutations for each category
for name_perm in itertools.permutations(names):
    for smoothie_perm in itertools.permutations(smoothies):
        for flower_perm in itertools.permutations(flowers):
            for animal_perm in itertools.permutations(animals):
                for hobby_perm in itertools.permutations(hobbies):
                    # Clue 8: Photography enthusiast is Eric
                    try:
                        p_idx = hobby_perm.index('photography')
                    except ValueError:
                        continue
                    if name_perm[p_idx] != 'Eric':
                        continue
                    # Clue 7: Watermelon lover keeps horses
                    if any(smoothie_perm[i] == 'watermelon' and animal_perm[i] != 'horse' for i in range(3)):
                        continue
                    # Clue 2: Bird keeper likes Cherry smoothies
                    if any(animal_perm[i] == 'bird' and smoothie_perm[i] != 'cherry' for i in range(3)):
                        continue
                    # Clue 3: Cooking lover is the Desert smoothie lover
                    if any(hobby_perm[i] == 'cooking' and smoothie_perm[i] != 'desert' for i in range(3)):
                        continue
                    # Clue 6: Daffodils lover is the Desert smoothie lover
                    if any(flower_perm[i] == 'daffodils' and smoothie_perm[i] != 'desert' for i in range(3)):
                        continue
                    # Clue 4: Gardening lover likes carnations
                    if any(hobby_perm[i] == 'gardening' and flower_perm[i] != 'carnations' for i in range(3)):
                        continue
                    # Clue 5: Cooking lover is directly left of Peter
                    try:
                        c_idx = hobby_perm.index('cooking')
                    except ValueError:
                        continue
                    if c_idx == 2:
                        continue
                    if name_perm[c_idx + 1] != 'Peter':
                        continue
                    # Clue 1: Horse keeper and photography enthusiast are next to each other
                    try:
                        h_idx = animal_perm.index('horse')
                    except ValueError:
                        continue
                    p_photography = hobby_perm.index('photography')
                    if abs(h_idx - p_photography) != 1:
                        continue

                    # Build solution
                    rows = []
                    for i in range(3):
                        house_num = str(i + 1)
                        name = name_perm[i]
                        smoothie = smoothie_perm[i]
                        flower = flower_perm[i]
                        animal = animal_perm[i]
                        hobby = hobby_perm[i]
                        rows.append([house_num, name, smoothie, flower, animal, hobby])

                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                            "rows": rows
                        }
                    }

                    print(json.dumps(solution))
                    exit()