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

    # Generate all possible permutations
    permutations = list(itertools.permutations(range(4)))

    # Check each permutation against the clues
    for name_perm in permutations:
        for flower_perm in permutations:
            for hobby_perm in permutations:
                for pet_perm in permutations:
                    for color_perm in permutations:
                        for house_style_perm in permutations:
                            # Unpack permutations for easier access
                            name_map = {i + 1: names[name_perm[i]] for i in range(4)}
                            flower_map = {i + 1: flowers[flower_perm[i]] for i in range(4)}
                            hobby_map = {i + 1: hobbies[hobby_perm[i]] for i in range(4)}
                            pet_map = {i + 1: pets[pet_perm[i]] for i in range(4)}
                            color_map = {i + 1: colors[color_perm[i]] for i in range(4)}
                            house_style_map = {i + 1: house_styles[house_style_perm[i]] for i in range(4)}

                            # Check each clue
                            if (house_style_map[2] == "craftsman" and
                                name_map[2] == "Arnold" and
                                (name_map.index("Peter") < flower_map.index("roses")) and
                                (hobby_map[pet_map.index("dog")] == "photography") and
                                (flower_map.index("daffodils") != 4) and
                                (color_map[flower_map.index("roses")] == "red") and
                                (color_map[name_map.index("Arnold")] == "red") and
                                (color_map[pet_map.index("fish")] == "white") and
                                (hobby_map.index("cooking") > color_map.index("red")) and
                                (color_map.index("white") == flower_map.index("carnations")) and
                                (color_map.index("white") > hobby_map.index("gardening")) and
                                (color_map[flower_map.index("daffodils")] == "yellow") and
                                (color_map[house_style_map.index("colonial")] == "red") and
                                (pet_map[name_map.index("Eric")] == "cat") and
                                (house_style_map[name_map.index("Eric")] == "victorian")):

                                # If all clues are satisfied, construct the solution
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
                                        "rows": [
                                            [str(house), name_map[house], flower_map[house], hobby_map[house], pet_map[house], color_map[house], house_style_map[house]]
                                            for house in range(1, 5)
                                        ]
                                    }
                                }

                                return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())