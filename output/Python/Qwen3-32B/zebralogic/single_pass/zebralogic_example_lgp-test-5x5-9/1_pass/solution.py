import itertools
import json

def main():
    # Define all possible values
    names_list = ['Bob', 'Arnold', 'Peter', 'Alice', 'Eric']
    drinks_list = ['milk', 'root beer', 'coffee', 'tea', 'water']
    colors_list = ['blue', 'green', 'white', 'yellow', 'red']
    flowers_list = ['daffodils', 'roses', 'lilies', 'tulips', 'carnations']
    hobbies_list = ['painting', 'cooking', 'photography', 'gardening', 'knitting']

    # Generate permutations with fixed constraints
    names_perms = []
    for p in itertools.permutations(names_list):
        if p[2] == 'Peter' and p[3] != 'Alice':
            names_perms.append(p)

    drinks_perms = []
    for p in itertools.permutations(drinks_list):
        if p[2] == 'water':
            drinks_perms.append(p)

    colors_perms = []
    for p in itertools.permutations(colors_list):
        if p[1] == 'white':
            colors_perms.append(p)

    flowers_perms = []
    for p in itertools.permutations(flowers_list):
        if p[1] == 'roses':
            flowers_perms.append(p)

    hobbies_perms = list(itertools.permutations(hobbies_list))

    # Check all combinations
    for names in names_perms:
        for drinks in drinks_perms:
            for colors in colors_perms:
                for flowers in flowers_perms:
                    for hobbies in hobbies_perms:
                        # Check all clues
                        valid = True

                        # Clue 2: root beer → gardening
                        for i in range(5):
                            if drinks[i] == 'root beer' and hobbies[i] != 'gardening':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 3: green → coffee
                        for i in range(5):
                            if colors[i] == 'green' and drinks[i] != 'coffee':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 4: green → lilies
                        for i in range(5):
                            if colors[i] == 'green' and flowers[i] != 'lilies':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 5: blue is to the right of daffodils
                        blue_pos = None
                        for i in range(5):
                            if colors[i] == 'blue':
                                blue_pos = i
                                break
                        daff_pos = None
                        for i in range(5):
                            if flowers[i] == 'daffodils':
                                daff_pos = i
                                break
                        if blue_pos is None or daff_pos is None or blue_pos <= daff_pos:
                            valid = False
                        if not valid:
                            continue

                        # Clue 6: cooking → blue
                        for i in range(5):
                            if hobbies[i] == 'cooking' and colors[i] != 'blue':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 7: Eric directly left of tea
                        eric_pos = None
                        for i in range(5):
                            if names[i] == 'Eric':
                                eric_pos = i
                                break
                        if eric_pos is None or eric_pos + 1 >= 5 or drinks[eric_pos + 1] != 'tea':
                            valid = False
                        if not valid:
                            continue

                        # Clue 9: Arnold's hobby is photography
                        arnold_pos = None
                        for i in range(5):
                            if names[i] == 'Arnold':
                                arnold_pos = i
                                break
                        if arnold_pos is None or hobbies[arnold_pos] != 'photography':
                            valid = False
                        if not valid:
                            continue

                        # Clue 11: carnations and red separated by one
                        carn_pos = None
                        for i in range(5):
                            if flowers[i] == 'carnations':
                                carn_pos = i
                                break
                        red_pos = None
                        for i in range(5):
                            if colors[i] == 'red':
                                red_pos = i
                                break
                        if carn_pos is None or red_pos is None or abs(carn_pos - red_pos) != 2:
                            valid = False
                        if not valid:
                            continue

                        # Clue 12: cooking left of painting
                        try:
                            cooking_pos = hobbies.index('cooking')
                            painting_pos = hobbies.index('painting')
                            if cooking_pos >= painting_pos:
                                valid = False
                        except ValueError:
                            valid = False
                        if not valid:
                            continue

                        # Clue 14: carnations → root beer
                        for i in range(5):
                            if flowers[i] == 'carnations' and drinks[i] != 'root beer':
                                valid = False
                                break
                        if not valid:
                            continue

                        # If all checks passed, build the solution
                        solution_rows = []
                        for i in range(5):
                            house_num = str(i + 1)
                            name = names[i]
                            drink = drinks[i]
                            color = colors[i]
                            flower = flowers[i]
                            hobby = hobbies[i]
                            solution_rows.append([house_num, name, drink, color, flower, hobby])
                        
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
                                "rows": solution_rows
                            }
                        }
                        print(json.dumps(solution))
                        return

if __name__ == "__main__":
    main()