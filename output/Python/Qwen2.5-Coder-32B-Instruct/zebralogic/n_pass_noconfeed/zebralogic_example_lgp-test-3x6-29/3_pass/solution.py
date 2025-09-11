import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3]
    names = ['Arnold', 'Peter', 'Eric']
    animals = ['bird', 'horse', 'cat']
    birthdays = ['jan', 'sept', 'april']
    hobbies = ['photography', 'cooking', 'gardening']
    drinks = ['milk', 'water', 'tea']
    hair_colors = ['black', 'brown', 'blonde']

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for animal_perm in itertools.permutations(animals):
            for birthday_perm in itertools.permutations(birthdays):
                for hobby_perm in itertools.permutations(hobbies):
                    for drink_perm in itertools.permutations(drinks):
                        for hair_color_perm in itertools.permutations(hair_colors):
                            # Create a dictionary to store the current permutation
                            solution = {
                                1: {'Name': name_perm[0], 'Animal': animal_perm[0], 'Birthday': birthday_perm[0], 'Hobby': hobby_perm[0], 'Drink': drink_perm[0], 'HairColor': hair_color_perm[0]},
                                2: {'Name': name_perm[1], 'Animal': animal_perm[1], 'Birthday': birthday_perm[1], 'Hobby': hobby_perm[1], 'Drink': drink_perm[1], 'HairColor': hair_color_perm[1]},
                                3: {'Name': name_perm[2], 'Animal': animal_perm[2], 'Birthday': birthday_perm[2], 'Hobby': hobby_perm[2], 'Drink': drink_perm[2], 'HairColor': hair_color_perm[2]}
                            }

                            # Check constraints
                            if (sum(1 for h in houses if solution[h]['HairColor'] == 'brown' and solution[h]['Hobby'] == 'cooking') == 1) and \
                               (sum(1 for h in houses if solution[h]['Birthday'] == 'april') == 1) and \
                               solution[3]['Name'] == 'Eric' and \
                               (sum(1 for h in houses if solution[h]['Animal'] == 'cat') == 1) and \
                               (sum(1 for h in houses if solution[h]['HairColor'] == 'blonde' and solution[h]['Drink'] == 'milk') == 1) and \
                               (sum(1 for h in houses if solution[h]['Hobby'] == 'gardening' and solution[h]['Drink'] == 'milk') == 1) and \
                               (sum(1 for h in houses if solution[h]['Animal'] == 'cat' and solution[h]['HairColor'] == 'brown') == 1) and \
                               solution[1]['Name'] == 'Arnold' and solution[1]['Animal'] == 'bird' and \
                               solution[2]['Drink'] == 'water' and solution[2]['Hobby'] == 'photography' and \
                               solution[2]['Birthday'] == 'sept':
                                # If all constraints are satisfied, format the solution
                                result = {
                                    "solution": {
                                        "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
                                        "rows": [
                                            [str(house), solution[house]['Name'], solution[house]['Animal'], solution[house]['Birthday'], solution[house]['Hobby'], solution[house]['Drink'], solution[house]['HairColor']] for house in houses
                                        ]
                                    }
                                }
                                print(json.dumps(result))
                                return

solve_puzzle()