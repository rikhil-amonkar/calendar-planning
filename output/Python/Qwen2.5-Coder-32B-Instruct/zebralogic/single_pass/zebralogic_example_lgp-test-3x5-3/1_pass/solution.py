import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ['Eric', 'Peter', 'Arnold']
    smoothies = ['cherry', 'watermelon', 'desert']
    flowers = ['carnations', 'lilies', 'daffodils']
    animals = ['cat', 'horse', 'bird']
    hobbies = ['photography', 'cooking', 'gardening']

    # Generate all possible permutations for each category
    permutations = list(itertools.permutations(names)) + \
                   list(itertools.permutations(smoothies)) + \
                   list(itertools.permutations(flowers)) + \
                   list(itertools.permutations(animals)) + \
                   list(itertools.permutations(hobbies))

    # Check all combinations of permutations
    for name_perm in permutations[:6]:
        for smoothie_perm in permutations[6:12]:
            for flower_perm in permutations[12:18]:
                for animal_perm in permutations[18:24]:
                    for hobby_perm in permutations[24:]:
                        # Unpack the permutations
                        name1, name2, name3 = name_perm
                        smoothie1, smoothie2, smoothie3 = smoothie_perm
                        flower1, flower2, flower3 = flower_perm
                        animal1, animal2, animal3 = animal_perm
                        hobby1, hobby2, hobby3 = hobby_perm

                        # Apply the clues
                        if (animal2 == 'horse' and hobby1 == 'photography') or \
                           (animal1 == 'horse' and hobby2 == 'photography') or \
                           (animal2 == 'horse' and hobby3 == 'photography') or \
                           (animal3 == 'horse' and hobby2 == 'photography'):
                            if animal3 == 'bird' and smoothie3 == 'cherry':
                                if hobby2 == 'cooking' and smoothie2 == 'desert':
                                    if hobby3 == 'gardening' and flower3 == 'carnations':
                                        if hobby2 == 'cooking' and name2 == 'Peter':
                                            if flower2 == 'daffodils' and smoothie2 == 'desert':
                                                if smoothie1 == 'watermelon' and animal1 == 'horse':
                                                    if hobby1 == 'photography' and name1 == 'Eric':
                                                        # If all conditions are met, construct the solution
                                                        solution = {
                                                            "solution": {
                                                                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                                                                "rows": [
                                                                    ["1", name1, smoothie1, flower1, animal1, hobby1],
                                                                    ["2", name2, smoothie2, flower2, animal2, hobby2],
                                                                    ["3", name3, smoothie3, flower3, animal3, hobby3]
                                                                ]
                                                            }
                                                        }
                                                        return json.dumps(solution)

# Print the solution
print(solve_puzzle())