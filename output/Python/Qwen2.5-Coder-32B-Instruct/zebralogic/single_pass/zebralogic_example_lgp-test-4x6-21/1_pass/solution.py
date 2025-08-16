import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Peter", "Arnold", "Alice", "Eric"]
    flowers = ["roses", "daffodils", "carnations", "lilies"]
    hobbies = ["photography", "painting", "cooking", "gardening"]
    pets = ["dog", "fish", "bird", "cat"]
    colors = ["red", "yellow", "green", "white"]
    house_styles = ["craftsman", "colonial", "ranch", "victorian"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(range(4)))

    # Iterate through all possible combinations
    for name_perm in all_permutations:
        for flower_perm in all_permutations:
            for hobby_perm in all_permutations:
                for pet_perm in all_permutations:
                    for color_perm in all_permutations:
                        for house_style_perm in all_permutations:
                            # Unpack permutations into lists for easier access
                            names_list = [names[i] for i in name_perm]
                            flowers_list = [flowers[i] for i in flower_perm]
                            hobbies_list = [hobbies[i] for i in hobby_perm]
                            pets_list = [pets[i] for i in pet_perm]
                            colors_list = [colors[i] for i in color_perm]
                            house_styles_list = [house_styles[i] for i in house_style_perm]

                            # Check each clue
                            if (
                                # Clue 1 & 6: The person in a Craftsman-style house is Arnold and in the second house.
                                house_styles_list[1] == "craftsman" and names_list[1] == "Arnold" and
                                # Clue 2: The person who loves the rose bouquet is somewhere to the right of Peter.
                                (names_list.index("Peter") < flowers_list.index("roses")) and
                                # Clue 3: The photography enthusiast is the person who owns a dog.
                                (hobbies_list.index("photography") == pets_list.index("dog")) and
                                # Clue 4: The person who loves a bouquet of daffodils is not in the fourth house.
                                (flowers_list[3] != "daffodils") and
                                # Clue 5: The person who loves the rose bouquet is the person whose favorite color is red.
                                (flowers_list.index("roses") == colors_list.index("red")) and
                                # Clue 7: Eric is the person residing in a Victorian house.
                                (house_styles_list[name_perm.index("Eric")] == "victorian") and
                                # Clue 8: The person with an aquarium of fish is the person who loves white.
                                (pets_list.index("fish") == colors_list.index("white")) and
                                # Clue 9: The person who loves cooking is somewhere to the right of the person whose favorite color is red.
                                (colors_list.index("red") < hobbies_list.index("cooking")) and
                                # Clue 10: The person who loves white is the person who loves a carnations arrangement.
                                (colors_list.index("white") == flowers_list.index("carnations")) and
                                # Clue 11: The person who loves white is somewhere to the right of the person who enjoys gardening.
                                (hobbies_list.index("gardening") < colors_list.index("white")) and
                                # Clue 12: The person who loves a bouquet of daffodils is the person who loves yellow.
                                (flowers_list.index("daffodils") == colors_list.index("yellow")) and
                                # Clue 13: The person living in a colonial-style house is the person whose favorite color is red.
                                (house_styles_list.index("colonial") == colors_list.index("red")) and
                                # Clue 14: The person who has a cat is Eric.
                                (pets_list[name_perm.index("Eric")] == "cat")
                            ):
                                # If all clues are satisfied, construct the solution
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
                                        "rows": [
                                            [str(i+1), names_list[i], flowers_list[i], hobbies_list[i], pets_list[i], colors_list[i], house_styles_list[i]]
                                            for i in range(4)
                                        ]
                                    }
                                }
                                return json.dumps(solution, indent=2)

# Print the solution as JSON
print(solve_puzzle())