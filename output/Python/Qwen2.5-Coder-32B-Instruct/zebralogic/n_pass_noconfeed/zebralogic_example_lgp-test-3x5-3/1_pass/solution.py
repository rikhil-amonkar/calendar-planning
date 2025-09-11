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
    permutations = list(itertools.permutations(names))
    permutations += list(itertools.permutations(smoothies))
    permutations += list(itertools.permutations(flowers))
    permutations += list(itertools.permutations(animals))
    permutations += list(itertools.permutations(hobbies))

    # Function to check if a given permutation satisfies all the clues
    def is_valid_solution(name_perm, smoothie_perm, flower_perm, animal_perm, hobby_perm):
        # Unpack the permutations into individual lists
        name1, name2, name3 = name_perm
        smoothie1, smoothie2, smoothie3 = smoothie_perm
        flower1, flower2, flower3 = flower_perm
        animal1, animal2, animal3 = animal_perm
        hobby1, hobby2, hobby3 = hobby_perm

        # Apply each clue to check validity
        # Clue 1: The person who keeps horses and the photography enthusiast are next to each other.
        if (animal1 == 'horse' and hobby2 == 'photography') or \
           (animal2 == 'horse' and (hobby1 == 'photography' or hobby3 == 'photography')) or \
           (animal3 == 'horse' and hobby2 == 'photography'):
            pass
        else:
            return False

        # Clue 2: The bird keeper is the person who likes Cherry smoothies.
        if (animal1 == 'bird' and smoothie1 == 'cherry') or \
           (animal2 == 'bird' and smoothie2 == 'cherry') or \
           (animal3 == 'bird' and smoothie3 == 'cherry'):
            pass
        else:
            return False

        # Clue 3: The person who loves cooking is the Desert smoothie lover.
        if (hobby1 == 'cooking' and smoothie1 == 'desert') or \
           (hobby2 == 'cooking' and smoothie2 == 'desert') or \
           (hobby3 == 'cooking' and smoothie3 == 'desert'):
            pass
        else:
            return False

        # Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
        if (hobby1 == 'gardening' and flower1 == 'carnations') or \
           (hobby2 == 'gardening' and flower2 == 'carnations') or \
           (hobby3 == 'gardening' and flower3 == 'carnations'):
            pass
        else:
            return False

        # Clue 5: The person who loves cooking is directly left of Peter.
        if (hobby1 == 'cooking' and name2 == 'Peter') or \
           (hobby2 == 'cooking' and name3 == 'Peter'):
            pass
        else:
            return False

        # Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
        if (flower1 == 'daffodils' and smoothie1 == 'desert') or \
           (flower2 == 'daffodils' and smoothie2 == 'desert') or \
           (flower3 == 'daffodils' and smoothie3 == 'desert'):
            pass
        else:
            return False

        # Clue 7: The Watermelon smoothie lover is the person who keeps horses.
        if (smoothie1 == 'watermelon' and animal1 == 'horse') or \
           (smoothie2 == 'watermelon' and animal2 == 'horse') or \
           (smoothie3 == 'watermelon' and animal3 == 'horse'):
            pass
        else:
            return False

        # Clue 8: The photography enthusiast is Eric.
        if (hobby1 == 'photography' and name1 == 'Eric') or \
           (hobby2 == 'photography' and name2 == 'Eric') or \
           (hobby3 == 'photography' and name3 == 'Eric'):
            pass
        else:
            return False

        return True

    # Iterate through all possible combinations of permutations
    for name_perm in permutations[:6]:
        for smoothie_perm in permutations[6:12]:
            for flower_perm in permutations[12:18]:
                for animal_perm in permutations[18:24]:
                    for hobby_perm in permutations[24:]:
                        if is_valid_solution(name_perm, smoothie_perm, flower_perm, animal_perm, hobby_perm):
                            # Construct the solution in the required format
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                                    "rows": [
                                        ["1", name_perm[0], smoothie_perm[0], flower_perm[0], animal_perm[0], hobby_perm[0]],
                                        ["2", name_perm[1], smoothie_perm[1], flower_perm[1], animal_perm[1], hobby_perm[1]],
                                        ["3", name_perm[2], smoothie_perm[2], flower_perm[2], animal_perm[2], hobby_perm[2]]
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())