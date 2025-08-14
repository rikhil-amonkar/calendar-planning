#!/usr/bin/env python3
import itertools
import json
import sys

def main():
    # Define the domains for each attribute
    names_domain = ['Peter', 'Arnold', 'Alice', 'Eric']
    flowers_domain = ['roses', 'daffodils', 'carnations', 'lilies']
    hobbies_domain = ['photography', 'painting', 'cooking', 'gardening']
    pets_domain = ['dog', 'fish', 'bird', 'cat']
    colors_domain = ['red', 'yellow', 'green', 'white']
    styles_domain = ['craftsman', 'colonial', 'ranch', 'victorian']

    # Houses are indexed from 0 to 3 corresponding to houses 1 to 4.
    # We use backtracking over all permutations and check each constraint.
    for names in itertools.permutations(names_domain):
        # Constraint 1 & 6: The Craftsman-style house (style) is in the second house and is Arnold.
        # So house index 1 must have name "Arnold".
        if names[1] != "Arnold":
            continue

        for styles in itertools.permutations(styles_domain):
            # House 2 (index 1) must be craftsman.
            if styles[1] != "craftsman":
                continue
            # Constraint 7: Eric lives in a Victorian house.
            valid = True
            for i in range(4):
                if names[i] == "Eric" and styles[i] != "victorian":
                    valid = False
                    break
            if not valid:
                continue

            for colors in itertools.permutations(colors_domain):
                # Constraint 13: The person living in a colonial-style house has favorite color red.
                valid_color = True
                for i in range(4):
                    if styles[i] == "colonial" and colors[i] != "red":
                        valid_color = False
                        break
                if not valid_color:
                    continue

                for flowers in itertools.permutations(flowers_domain):
                    # Constraint 5: The person who loves the roses must have red as favorite color.
                    # Constraint 12: The person who loves daffodils must have yellow as favorite color.
                    valid_flower = True
                    for i in range(4):
                        if flowers[i] == "roses" and colors[i] != "red":
                            valid_flower = False
                            break
                        if flowers[i] == "daffodils" and colors[i] != "yellow":
                            valid_flower = False
                            break
                    if not valid_flower:
                        continue

                    # Constraint 4: The house with the daffodils bouquet is not in the fourth house.
                    if flowers[3] == "daffodils":
                        continue

                    # Constraint 2: The person who loves the rose bouquet is somewhere to the right of Peter.
                    try:
                        index_peter = names.index("Peter")
                        index_roses = flowers.index("roses")
                    except ValueError:
                        continue
                    if index_roses <= index_peter:
                        continue

                    for hobbies in itertools.permutations(hobbies_domain):
                        # Constraint 9: The person who loves cooking is somewhere to the right of the person whose favorite color is red.
                        cooking_index = hobbies.index("cooking")
                        red_index = colors.index("red")
                        if cooking_index <= red_index:
                            continue

                        # Constraint 11: The person who loves white is somewhere to the right of the person who enjoys gardening.
                        white_index = colors.index("white")
                        gardening_index = hobbies.index("gardening")
                        if white_index <= gardening_index:
                            continue

                        for pets in itertools.permutations(pets_domain):
                            # Constraint 3: The photography enthusiast is the person who owns a dog.
                            valid_pet = True
                            for i in range(4):
                                if hobbies[i] == "photography" and pets[i] != "dog":
                                    valid_pet = False
                                    break
                                if pets[i] == "dog" and hobbies[i] != "photography":
                                    valid_pet = False
                                    break
                            if not valid_pet:
                                continue

                            # Constraint 8: The person with an aquarium of fish is the person who loves white.
                            valid_pet_color = True
                            for i in range(4):
                                if pets[i] == "fish" and colors[i] != "white":
                                    valid_pet_color = False
                                    break
                                if colors[i] == "white" and pets[i] != "fish":
                                    valid_pet_color = False
                                    break
                            if not valid_pet_color:
                                continue

                            # Constraint 10: The person who loves white is the person who loves a carnations arrangement.
                            valid_white_flower = True
                            for i in range(4):
                                if colors[i] == "white" and flowers[i] != "carnations":
                                    valid_white_flower = False
                                    break
                                if flowers[i] == "carnations" and colors[i] != "white":
                                    valid_white_flower = False
                                    break
                            if not valid_white_flower:
                                continue

                            # Constraint 14: The person who has a cat is Eric.
                            valid_cat = True
                            for i in range(4):
                                if pets[i] == "cat" and names[i] != "Eric":
                                    valid_cat = False
                                    break
                            if not valid_cat:
                                continue

                            # If all constraints pass, we have found the unique solution.
                            solution = []
                            for i in range(4):
                                # House numbers are 1-indexed.
                                house_number = str(i + 1)
                                row = [
                                    house_number,
                                    names[i],
                                    flowers[i],
                                    hobbies[i],
                                    pets[i],
                                    colors[i],
                                    styles[i]
                                ]
                                solution.append(row)
                            header = ["House", "Name", "Flower", "Hobby", "Pet", "Color", "House style"]
                            result = {"solution": {"header": header, "rows": solution}}
                            print(json.dumps(result, indent=2))
                            sys.exit(0)

if __name__ == '__main__':
    main()