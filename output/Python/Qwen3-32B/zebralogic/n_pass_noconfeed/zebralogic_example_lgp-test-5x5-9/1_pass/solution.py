import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ['Bob', 'Arnold', 'Peter', 'Alice', 'Eric']
    drinks = ['milk', 'root beer', 'coffee', 'tea', 'water']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    flowers = ['daffodils', 'roses', 'lilies', 'tulips', 'carnations']
    hobbies = ['painting', 'cooking', 'photography', 'gardening', 'knitting']

    # Generate possible permutations with fixed positions
    possible_names = []
    for p in itertools.permutations(names):
        if p[2] == 'Peter':  # house 3 (0-based index 2)
            possible_names.append(p)

    possible_drinks = []
    for p in itertools.permutations(drinks):
        if p[2] == 'water':  # house 3
            possible_drinks.append(p)

    possible_colors = []
    for p in itertools.permutations(colors):
        if p[1] == 'white':  # house 2 (index 1)
            possible_colors.append(p)

    possible_flowers = []
    for p in itertools.permutations(flowers):
        if p[1] == 'roses':  # house 2
            possible_flowers.append(p)

    possible_hobbies = list(itertools.permutations(hobbies))  # no fixed positions

    # Now iterate through all combinations
    for name_p in possible_names:
        for drink_p in possible_drinks:
            for color_p in possible_colors:
                for flower_p in possible_flowers:
                    for hobby_p in possible_hobbies:
                        # Constraint 1: Alice is not in house 4 (index 3)
                        if name_p[3] == 'Alice':
                            continue

                        # Constraint 2: root beer → gardening
                        valid2 = True
                        for i in range(5):
                            if drink_p[i] == 'root beer' and hobby_p[i] != 'gardening':
                                valid2 = False
                                break
                        if not valid2:
                            continue

                        # Constraint 3 and 4: green → coffee and lilies
                        valid3_4 = True
                        for i in range(5):
                            if color_p[i] == 'green':
                                if drink_p[i] != 'coffee' or flower_p[i] != 'lilies':
                                    valid3_4 = False
                                    break
                        if not valid3_4:
                            continue

                        # Constraint 5: blue is to the right of daffodils
                        blue_idx = color_p.index('blue')
                        daffodils_idx = flower_p.index('daffodils')
                        if blue_idx <= daffodils_idx:
                            continue

                        # Constraint 6: cooking → blue
                        valid6 = True
                        for i in range(5):
                            if hobby_p[i] == 'cooking' and color_p[i] != 'blue':
                                valid6 = False
                                break
                        if not valid6:
                            continue

                        # Constraint 7: Eric is directly left of tea
                        eric_idx = -1
                        try:
                            eric_idx = name_p.index('Eric')
                        except ValueError:
                            pass
                        if eric_idx != -1:
                            if eric_idx + 1 >= 5 or drink_p[eric_idx + 1] != 'tea':
                                continue

                        # Constraint 9: Arnold's hobby is photography
                        arnold_idx = name_p.index('Arnold')
                        if hobby_p[arnold_idx] != 'photography':
                            continue

                        # Constraint 11: carnations and red have one house between
                        carnations_idx = flower_p.index('carnations')
                        red_idx = color_p.index('red')
                        if abs(carnations_idx - red_idx) != 2:
                            continue

                        # Constraint 12: cooking is left of painting
                        cooking_idx = hobby_p.index('cooking')
                        painting_idx = hobby_p.index('painting')
                        if cooking_idx >= painting_idx:
                            continue

                        # Constraint 14: carnations → root beer
                        valid14 = True
                        for i in range(5):
                            if flower_p[i] == 'carnations' and drink_p[i] != 'root beer':
                                valid14 = False
                                break
                        if not valid14:
                            continue

                        # If all constraints passed, build the solution
                        solution_rows = []
                        for i in range(5):
                            house_num = i + 1
                            row = [
                                str(house_num),
                                name_p[i],
                                drink_p[i],
                                color_p[i],
                                flower_p[i],
                                hobby_p[i]
                            ]
                            solution_rows.append(row)

                        # Return the solution as JSON
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
                                "rows": solution_rows
                            }
                        }

                        print(json.dumps(solution))
                        return

    # If no solution found (unlikely)
    print(json.dumps({"solution": None}))

if __name__ == "__main__":
    solve_puzzle()