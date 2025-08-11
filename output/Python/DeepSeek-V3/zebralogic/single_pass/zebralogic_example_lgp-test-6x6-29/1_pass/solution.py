import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    categories = {
        'House': ['1', '2', '3', '4', '5', '6'],
        'Name': ['Arnold', 'Carol', 'Peter', 'Eric', 'Bob', 'Alice'],
        'House Style': ['ranch', 'colonial', 'modern', 'craftsman', 'mediterranean', 'victorian'],
        'Lunch': ['pizza', 'stew', 'spaghetti', 'grilled cheese', 'stir fry', 'soup'],
        'Vacation': ['cultural', 'cruise', 'mountain', 'camping', 'city', 'beach'],
        'Height': ['average', 'very tall', 'very short', 'short', 'tall', 'super tall'],
        'Cigar': ['yellow monster', 'prince', 'dunhill', 'pall mall', 'blue master', 'blends']
    }

    # Initialize the solution structure
    solution = {
        "solution": {
            "header": ['House', 'Name', 'House Style', 'Lunch', 'Vacation', 'Height', 'Cigar'],
            "rows": []
        }
    }

    # Helper function to find index of a value in a list
    def find_index(lst, val):
        try:
            return lst.index(val)
        except ValueError:
            return -1

    # Generate all possible permutations for each category
    for names in permutations(categories['Name']):
        # Check clue 1: Alice is in the fifth house.
        if names[4] != 'Alice':
            continue

        # Check clue 9: Eric is in the fourth house.
        if names[3] != 'Eric':
            continue

        for house_styles in permutations(categories['House Style']):
            # Check clue 6: Craftsman is not in the third house.
            if house_styles[2] == 'craftsman':
                continue

            # Check clue 18: Modern is left of Alice (house 5)
            modern_index = find_index(house_styles, 'modern')
            if modern_index == -1 or modern_index >= 4:
                continue

            # Check clue 14: Alice is in Victorian house (from clue 3 and 14)
            if house_styles[4] != 'victorian':
                continue

            # Check clue 2 and 7: stir fry is colonial and average height
            # Check clue 17: stir fry is directly left of Bob
            for lunch in permutations(categories['Lunch']):
                if lunch[4] != 'spaghetti':  # clue 3: Alice loves spaghetti
                    continue

                stir_fry_index = find_index(lunch, 'stir fry')
                if stir_fry_index == -1:
                    continue

                # Check clue 2: stir fry is colonial
                if house_styles[stir_fry_index] != 'colonial':
                    continue

                # Check clue 17: stir fry is directly left of Bob
                if stir_fry_index + 1 >= 6 or names[stir_fry_index + 1] != 'Bob':
                    continue

                # Check clue 20: stir fry is left of prince smoker
                # We'll check this later with cigar assignments

                for vacation in permutations(categories['Vacation']):
                    # Check clue 10: one house between colonial and camping
                    colonial_index = find_index(house_styles, 'colonial')
                    if colonial_index == -1:
                        continue
                    if colonial_index + 2 >= 6 or vacation[colonial_index + 2] != 'camping':
                        continue

                    # Check clue 8: beach is ranch
                    # Check clue 15: tall loves beach
                    # Check clue 22: ranch smokes blue master
                    # Check clue 23: blends is directly left of blue master
                    ranch_index = find_index(house_styles, 'ranch')
                    if ranch_index != -1:
                        if vacation[ranch_index] != 'beach':
                            continue

                    # Check clue 24: cultural is pizza
                    # Check clue 25: pizza is left of cruise
                    pizza_index = find_index(lunch, 'pizza')
                    if pizza_index != -1:
                        if vacation[pizza_index] != 'cultural':
                            continue
                        cruise_index = find_index(vacation, 'cruise')
                        if cruise_index != -1 and cruise_index <= pizza_index:
                            continue

                    for height in permutations(categories['Height']):
                        # Check clue 7: average height is stir fry
                        if height[stir_fry_index] != 'average':
                            continue

                        # Check clue 5: one house between average and Peter
                        peter_index = find_index(names, 'Peter')
                        if peter_index == -1:
                            continue
                        if abs(peter_index - stir_fry_index) != 2:
                            continue

                        # Check clue 11: mountain is yellow monster
                        # Check clue 12: mountain is very tall
                        mountain_index = find_index(vacation, 'mountain')
                        if mountain_index != -1:
                            if height[mountain_index] != 'very tall':
                                continue

                        # Check clue 15: tall loves beach
                        beach_index = find_index(vacation, 'beach')
                        if beach_index != -1:
                            if height[beach_index] != 'tall':
                                continue

                        # Check clue 16: tall is left of victorian (house 5)
                        tall_index = find_index(height, 'tall')
                        if tall_index != -1 and tall_index >= 4:
                            continue

                        # Check clue 19: craftsman is left of short
                        craftsman_index = find_index(house_styles, 'craftsman')
                        short_index = find_index(height, 'short')
                        if craftsman_index != -1 and short_index != -1:
                            if craftsman_index >= short_index:
                                continue

                        # Check clue 21: two houses between grilled cheese and super tall
                        grilled_cheese_index = find_index(lunch, 'grilled cheese')
                        super_tall_index = find_index(height, 'super tall')
                        if grilled_cheese_index != -1 and super_tall_index != -1:
                            if abs(super_tall_index - grilled_cheese_index) != 3:
                                continue

                        for cigar in permutations(categories['Cigar']):
                            # Check clue 11: mountain is yellow monster
                            if mountain_index != -1 and cigar[mountain_index] != 'yellow monster':
                                continue

                            # Check clue 13: mountain and dunhill are next to each other
                            if mountain_index != -1:
                                adjacent = False
                                if mountain_index > 0 and cigar[mountain_index - 1] == 'dunhill':
                                    adjacent = True
                                if mountain_index < 5 and cigar[mountain_index + 1] == 'dunhill':
                                    adjacent = True
                                if not adjacent:
                                    continue

                            # Check clue 20: stir fry is left of prince
                            prince_index = find_index(cigar, 'prince')
                            if prince_index != -1 and prince_index <= stir_fry_index:
                                continue

                            # Check clue 22: ranch smokes blue master
                            if ranch_index != -1 and cigar[ranch_index] != 'blue master':
                                continue

                            # Check clue 23: blends is directly left of blue master
                            if ranch_index != -1 and ranch_index > 0 and cigar[ranch_index - 1] != 'blends':
                                continue

                            # Check clue 4: Arnold loves stew
                            arnold_index = find_index(names, 'Arnold')
                            if arnold_index != -1 and lunch[arnold_index] != 'stew':
                                continue

                            # All clues satisfied, construct the solution
                            rows = []
                            for i in range(6):
                                row = [
                                    str(i + 1),
                                    names[i],
                                    house_styles[i],
                                    lunch[i],
                                    vacation[i],
                                    height[i],
                                    cigar[i]
                                ]
                                rows.append(row)
                            solution['solution']['rows'] = rows
                            return json.dumps(solution, indent=2)

    return json.dumps(solution, indent=2)

print(solve_puzzle())