import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ['Bob', 'Arnold', 'Peter', 'Alice', 'Eric']
    drinks = ['milk', 'root beer', 'coffee', 'tea', 'water']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    flowers = ['daffodils', 'roses', 'lilies', 'tulips', 'carnations']
    hobbies = ['painting', 'cooking', 'photography', 'gardening', 'knitting']

    all_combinations = list(itertools.permutations(range(5)))

    for name_order in all_combinations:
        for drink_order in all_combinations:
            for color_order in all_combinations:
                for flower_order in all_combinations:
                    for hobby_order in all_combinations:
                        # Create dictionaries for quick lookup
                        name_dict = {name: order for name, order in zip(names, name_order)}
                        drink_dict = {drink: order for drink, order in zip(drinks, drink_order)}
                        color_dict = {color: order for color, order in zip(colors, color_order)}
                        flower_dict = {flower: order for flower, order in zip(flowers, flower_order)}
                        hobby_dict = {hobby: order for hobby, order in zip(hobbies, hobby_order)}

                        # Check all clues
                        if (name_dict['Alice'] != 3 and  # Clue 1
                            drink_dict['root beer'] == hobby_dict['gardening'] and  # Clue 2
                            color_dict['green'] == drink_dict['coffee'] and  # Clue 3
                            color_dict['green'] == flower_dict['lilies'] and  # Clue 4
                            color_dict['blue'] > flower_dict['daffodils'] and  # Clue 5
                            hobby_dict['cooking'] == color_dict['blue'] and  # Clue 6
                            name_dict['Eric'] + 1 == drink_dict['tea'] and  # Clue 7
                            drink_dict['water'] == name_dict['Peter'] and  # Clue 8
                            hobby_dict['photography'] == name_dict['Arnold'] and  # Clue 9
                            color_dict['white'] == flower_dict['roses'] and  # Clue 10
                            abs(flower_dict['carnations'] - color_dict['red']) == 2 and  # Clue 11
                            hobby_dict['cooking'] < hobby_dict['painting'] and  # Clue 12
                            drink_dict['water'] == 2 and  # Clue 13
                            drink_dict['root beer'] == flower_dict['carnations'] and  # Clue 14
                            color_dict['white'] == 1):  # Clue 15

                            # Construct the solution
                            solution = []
                            for house in houses:
                                name = names[name_order.index(house - 1)]
                                drink = drinks[drink_order.index(house - 1)]
                                color = colors[color_order.index(house - 1)]
                                flower = flowers[flower_order.index(house - 1)]
                                hobby = hobbies[hobby_order.index(house - 1)]
                                solution.append([str(house), name, drink, color, flower, hobby])

                            return {
                                "solution": {
                                    "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
                                    "rows": solution
                                }
                            }

# Solve the puzzle and print the solution in JSON format
solution_json = solve_puzzle()
print(json.dumps(solution_json, indent=2))