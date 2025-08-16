import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4', '5']
    names = ['Bob', 'Arnold', 'Peter', 'Alice', 'Eric']
    drinks = ['milk', 'root beer', 'coffee', 'tea', 'water']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    flowers = ['daffodils', 'roses', 'lilies', 'tulips', 'carnations']
    hobbies = ['painting', 'cooking', 'photography', 'gardening', 'knitting']

    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for drink_perm in permutations(drinks):
            for color_perm in permutations(colors):
                for flower_perm in permutations(flowers):
                    for hobby_perm in permutations(hobbies):
                        # Assign each permutation to houses
                        solution = []
                        for i in range(5):
                            house = {
                                'House': str(i+1),
                                'Name': name_perm[i],
                                'Drink': drink_perm[i],
                                'Color': color_perm[i],
                                'Flower': flower_perm[i],
                                'Hobby': hobby_perm[i]
                            }
                            solution.append(house)

                        # Check all constraints
                        valid = True

                        # Constraint 1: Alice is not in the fourth house.
                        if solution[3]['Name'] == 'Alice':
                            valid = False

                        # Constraint 2: The root beer lover is the person who enjoys gardening.
                        for house in solution:
                            if house['Drink'] == 'root beer' and house['Hobby'] != 'gardening':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 3: The person whose favorite color is green is the coffee drinker.
                        for house in solution:
                            if house['Color'] == 'green' and house['Drink'] != 'coffee':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 4: The person whose favorite color is green is the person who loves the bouquet of lilies.
                        for house in solution:
                            if house['Color'] == 'green' and house['Flower'] != 'lilies':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 5: The person who loves blue is somewhere to the right of the person who loves a bouquet of daffodils.
                        blue_house = None
                        daffodils_house = None
                        for house in solution:
                            if house['Color'] == 'blue':
                                blue_house = int(house['House'])
                            if house['Flower'] == 'daffodils':
                                daffodils_house = int(house['House'])
                        if blue_house is None or daffodils_house is None or blue_house <= daffodils_house:
                            valid = False
                        if not valid:
                            continue

                        # Constraint 6: The person who loves cooking is the person who loves blue.
                        for house in solution:
                            if house['Hobby'] == 'cooking' and house['Color'] != 'blue':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 7: Eric is directly left of the tea drinker.
                        eric_pos = None
                        tea_pos = None
                        for i, house in enumerate(solution):
                            if house['Name'] == 'Eric':
                                eric_pos = i
                            if house['Drink'] == 'tea':
                                tea_pos = i
                        if eric_pos is None or tea_pos is None or tea_pos - eric_pos != 1:
                            valid = False
                        if not valid:
                            continue

                        # Constraint 8: The one who only drinks water is Peter.
                        for house in solution:
                            if house['Drink'] == 'water' and house['Name'] != 'Peter':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 9: Arnold is the photography enthusiast.
                        for house in solution:
                            if house['Name'] == 'Arnold' and house['Hobby'] != 'photography':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 10: The person who loves white is the person who loves the rose bouquet.
                        for house in solution:
                            if house['Color'] == 'white' and house['Flower'] != 'roses':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 11: There is one house between the person who loves a carnations arrangement and the person whose favorite color is red.
                        carnations_pos = None
                        red_pos = None
                        for i, house in enumerate(solution):
                            if house['Flower'] == 'carnations':
                                carnations_pos = i
                            if house['Color'] == 'red':
                                red_pos = i
                        if carnations_pos is None or red_pos is None or abs(carnations_pos - red_pos) != 2:
                            valid = False
                        if not valid:
                            continue

                        # Constraint 12: The person who loves cooking is somewhere to the left of the person who paints as a hobby.
                        cooking_pos = None
                        painting_pos = None
                        for i, house in enumerate(solution):
                            if house['Hobby'] == 'cooking':
                                cooking_pos = i
                            if house['Hobby'] == 'painting':
                                painting_pos = i
                        if cooking_pos is None or painting_pos is None or cooking_pos >= painting_pos:
                            valid = False
                        if not valid:
                            continue

                        # Constraint 13: The one who only drinks water is in the third house.
                        if solution[2]['Drink'] != 'water':
                            valid = False
                        if not valid:
                            continue

                        # Constraint 14: The person who loves a carnations arrangement is the root beer lover.
                        for house in solution:
                            if house['Flower'] == 'carnations' and house['Drink'] != 'root beer':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 15: The person who loves white is in the second house.
                        if solution[1]['Color'] != 'white':
                            valid = False
                        if not valid:
                            continue

                        # If all constraints are satisfied, return the solution
                        if valid:
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
                                    "rows": []
                                }
                            }
                            for house in solution:
                                row = [
                                    house['House'],
                                    house['Name'],
                                    house['Drink'],
                                    house['Color'],
                                    house['Flower'],
                                    house['Hobby']
                                ]
                                result["solution"]["rows"].append(row)
                            return json.dumps(result, indent=2)

    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())