import itertools
import json

# Define the possible values for each attribute
names = ['Arnold', 'Peter', 'Eric']
animals = ['bird', 'horse', 'cat']
birthdays = ['jan', 'sept', 'april']
hobbies = ['photography', 'cooking', 'gardening']
drinks = ['milk', 'water', 'tea']
haircolors = ['black', 'brown', 'blonde']

# Iterate through all possible permutations for each attribute
for name_perm in itertools.permutations(names):
    # Check clue 3: Eric not in first house
    if name_perm[0] == 'Eric':
        continue
    for animal_perm in itertools.permutations(animals):
        # Check clue 4: cat in second house
        if animal_perm[1] != 'cat':
            continue
        # Check clue 8: Arnold is bird keeper
        valid_clue8 = True
        bird_index = -1
        for i in range(3):
            if animal_perm[i] == 'bird':
                if name_perm[i] != 'Arnold':
                    valid_clue8 = False
                    break
                else:
                    if bird_index == -1:
                        bird_index = i
                    else:
                        valid_clue8 = False
                        break
        if not valid_clue8 or bird_index == -1:
            continue
        for birthday_perm in itertools.permutations(birthdays):
            # Check clue 2: third house has april
            if birthday_perm[2] != 'april':
                continue
            # Check clue 10: sept is directly left of Arnold
            sept_index = -1
            for i in range(3):
                if birthday_perm[i] == 'sept':
                    sept_index = i
                    break
            if sept_index == -1:
                continue
            if sept_index + 1 >= 3 or name_perm[sept_index + 1] != 'Arnold':
                continue
            for hobby_perm in itertools.permutations(hobbies):
                for drink_perm in itertools.permutations(drinks):
                    for hair_perm in itertools.permutations(haircolors):
                        # Check clue 1: brown hair implies cooking
                        clue1 = True
                        for i in range(3):
                            if hair_perm[i] == 'brown' and hobby_perm[i] != 'cooking':
                                clue1 = False
                                break
                        if not clue1:
                            continue
                        # Check clue 5: blonde is left of milk
                        blonde_index = hair_perm.index('blonde')
                        milk_index = drink_perm.index('milk')
                        if not (blonde_index < milk_index):
                            continue
                        # Check clue 6: gardening implies milk
                        clue6 = True
                        for i in range(3):
                            if hobby_perm[i] == 'gardening' and drink_perm[i] != 'milk':
                                clue6 = False
                                break
                        if not clue6:
                            continue
                        # Check clue 7: cat lover (house 2) has brown hair
                        if hair_perm[1] != 'brown':
                            continue
                        # Check clue 9: water implies photography
                        clue9 = True
                        for i in range(3):
                            if drink_perm[i] == 'water' and hobby_perm[i] != 'photography':
                                clue9 = False
                                break
                        if not clue9:
                            continue
                        # All constraints satisfied
                        # Build the solution
                        solution_rows = []
                        for i in range(3):
                            house_num = str(i + 1)
                            name = name_perm[i]
                            animal = animal_perm[i]
                            birthday = birthday_perm[i]
                            hobby = hobby_perm[i]
                            drink = drink_perm[i]
                            hair = hair_perm[i]
                            solution_rows.append([house_num, name, animal, birthday, hobby, drink, hair])
                        # Output as JSON
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
                                "rows": solution_rows
                            }
                        }
                        print(json.dumps(solution))
                        exit()