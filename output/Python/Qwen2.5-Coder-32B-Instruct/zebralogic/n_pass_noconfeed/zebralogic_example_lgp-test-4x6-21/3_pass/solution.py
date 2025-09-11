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

                            # Create reverse maps for easier lookup by value
                            name_reverse_map = {v: k for k, v in name_map.items()}
                            flower_reverse_map = {v: k for k, v in flower_map.items()}
                            pet_reverse_map = {v: k for k, v in pet_map.items()}
                            color_reverse_map = {v: k for k, v in color_map.items()}
                            house_style_reverse_map = {v: k for k, v in house_style_map.items()}
                            hobby_reverse_map = {v: k for k, v in hobby_map.items()}  # Added this line

                            # Check each clue
                            if (house_style_map[2] == "craftsman" and
                                name_map[2] == "Arnold" and
                                (name_reverse_map["Peter"] < flower_reverse_map["roses"]) and
                                (hobby_map[pet_reverse_map["dog"]] == "photography") and
                                (flower_reverse_map["daffodils"] != 4) and
                                (color_map[flower_reverse_map["roses"]] == "red") and
                                (color_map[name_reverse_map["Arnold"]] == "red") and
                                (color_map[pet_reverse_map["fish"]] == "white") and
                                (hobby_reverse_map["cooking"] > color_reverse_map["red"]) and
                                (color_reverse_map["white"] == flower_reverse_map["carnations"]) and
                                (color_reverse_map["white"] > hobby_reverse_map["gardening"]) and
                                (color_map[flower_reverse_map["daffodils"]] == "yellow") and
                                (color_map[house_style_reverse_map["colonial"]] == "red") and
                                (pet_map[name_reverse_map["Eric"]] == "cat") and
                                (house_style_map[name_reverse_map["Eric"]] == "victorian")):

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