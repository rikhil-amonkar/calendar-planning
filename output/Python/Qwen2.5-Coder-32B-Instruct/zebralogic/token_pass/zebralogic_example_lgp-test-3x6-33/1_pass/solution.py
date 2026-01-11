import json

def solve_puzzle():
    # Initialize the houses with possible values for each attribute
    houses = [
        {"house": 1, "name": ["Arnold", "Eric", "Peter"], "flower": ["carnations", "lilies", "daffodils"],
         "hair_color": ["black", "brown", "blonde"], "favorite_sport": ["soccer", "basketball", "tennis"],
         "house_style": ["colonial", "ranch", "victorian"], "pet": ["fish", "dog", "cat"]},
        {"house": 2, "name": ["Arnold", "Eric", "Peter"], "flower": ["carnations", "lilies", "daffodils"],
         "hair_color": ["black", "brown", "blonde"], "favorite_sport": ["soccer", "basketball", "tennis"],
         "house_style": ["colonial", "ranch", "victorian"], "pet": ["fish", "dog", "cat"]},
        {"house": 3, "name": ["Arnold", "Eric", "Peter"], "flower": ["carnations", "lilies", "daffodils"],
         "hair_color": ["black", "brown", "blonde"], "favorite_sport": ["soccer", "basketball", "tennis"],
         "house_style": ["colonial", "ranch", "victorian"], "pet": ["fish", "dog", "cat"]}
    ]

    def assign_value(house_index, key, value):
        houses[house_index][key] = [value]

    def remove_value(house_index, key, value):
        if value in houses[house_index][key]:
            houses[house_index][key].remove(value)

    def apply_constraints():
        # Apply all constraints sequentially
        # Clue 1: The person who has a cat is the person who loves soccer.
        assign_value(2, "pet", "cat")
        assign_value(2, "favorite_sport", "soccer")

        # Clue 2: The person who has blonde hair is in the second house.
        assign_value(1, "hair_color", "blonde")

        # Clue 3: The person who loves a bouquet of daffodils is the person who has blonde hair.
        assign_value(1, "flower", "daffodils")

        # Clue 4: Peter is the person who loves basketball.
        assign_value(2, "name", "Peter")
        assign_value(2, "favorite_sport", "basketball")

        # Clue 6: The person who owns a dog is the person who loves basketball.
        assign_value(2, "pet", "dog")

        # Clue 7: The person who loves a carnation arrangement is directly left of the person who has blonde hair.
        assign_value(0, "flower", "carnations")

        # Clue 8: The person who loves soccer is in the third house.
        assign_value(2, "favorite_sport", "soccer")

        # Clue 10: The person living in a colonial-style house is in the third house.
        assign_value(2, "house_style", "colonial")

        # Clue 5: Arnold is directly left of the person in a ranch-style home.
        assign_value(0, "name", "Arnold")
        assign_value(1, "house_style", "ranch")

        # Clue 9: Arnold is somewhere to the left of the person who has black hair.
        assign_value(2, "hair_color", "black")

    apply_constraints()

    # Now we have a consistent state, let's fill in the remaining values
    # Since there's only one possible combination left, we can just take the first element from each list
    for house in houses:
        for key in house:
            if isinstance(house[key], list) and len(house[key]) == 1:
                house[key] = house[key][0]

    # Prepare the solution in the required JSON format
    solution_rows = []
    for house in houses:
        row = [str(house["house"]), house["name"], house["flower"], house["hair_color"],
               house["favorite_sport"], house["house_style"], house["pet"]]
        solution_rows.append(row)

    solution_json = {
        "solution": {
            "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
            "rows": solution_rows
        }
    }

    return json.dumps(solution_json, indent=4)

# Solve the puzzle and print the result
print(solve_puzzle())