import json

def solve_puzzle():
    # Initialize the houses
    houses = [
        {"House": "1", "Name": None, "HouseStyle": None, "HairColor": None, "Children": None, "BookGenre": None},
        {"House": "2", "Name": None, "HouseStyle": None, "HairColor": None, "Children": None, "BookGenre": None},
        {"House": "3", "Name": None, "HouseStyle": None, "HairColor": None, "Children": None, "BookGenre": None},
        {"House": "4", "Name": None, "HouseStyle": None, "HairColor": None, "Children": None, "BookGenre": None}
    ]

    # Apply clues
    # Clue 1: The person in a Craftsman-style house is in the third house.
    houses[2]["HouseStyle"] = "craftsman"

    # Clue 2: Alice is the person who loves romance books.
    for house in houses:
        if house["Name"] == "Alice":
            house["BookGenre"] = "romance"
            break
    else:
        for house in houses:
            if house["BookGenre"] is None:
                house["BookGenre"] = "romance"
                house["Name"] = "Alice"
                break

    # Clue 3: The person who has brown hair is in the fourth house.
    houses[3]["HairColor"] = "brown"

    # Clue 4: The person's child is named Samantha is in the fourth house.
    houses[3]["Children"] = "Samantha"

    # Clue 5: The person in a ranch-style home is somewhere to the right of the person who has red hair.
    # This will be checked later after more information is available.

    # Clue 6: Peter is the person's child is named Bella.
    for house in houses:
        if house["Children"] == "Bella":
            house["Name"] = "Peter"
            break
    else:
        for house in houses:
            if house["Name"] is None:
                house["Name"] = "Peter"
                house["Children"] = "Bella"
                break

    # Clue 7: Arnold is the person who has red hair.
    for house in houses:
        if house["Name"] == "Arnold":
            house["HairColor"] = "red"
            break
    else:
        for house in houses:
            if house["HairColor"] is None:
                house["HairColor"] = "red"
                house["Name"] = "Arnold"
                break

    # Clue 8: Alice is the person living in a colonial-style house.
    for house in houses:
        if house["Name"] == "Alice":
            house["HouseStyle"] = "colonial"
            break
    else:
        for house in houses:
            if house["HouseStyle"] is None:
                house["HouseStyle"] = "colonial"
                house["Name"] = "Alice"
                break

    # Clue 9: The person who has black hair is in the second house.
    houses[1]["HairColor"] = "black"

    # Clue 10: The person who loves fantasy books is Peter.
    for house in houses:
        if house["Name"] == "Peter":
            house["BookGenre"] = "fantasy"
            break
    else:
        for house in houses:
            if house["BookGenre"] is None:
                house["BookGenre"] = "fantasy"
                house["Name"] = "Peter"
                break

    # Clue 11: Arnold is the person's child is named Meredith.
    for house in houses:
        if house["Children"] == "Meredith":
            house["Name"] = "Arnold"
            break
    else:
        for house in houses:
            if house["Name"] is None:
                house["Name"] = "Arnold"
                house["Children"] = "Meredith"
                break

    # Clue 12: The person who has black hair is Eric.
    for house in houses:
        if house["HairColor"] == "black":
            house["Name"] = "Eric"
            break
    else:
        for house in houses:
            if house["Name"] is None:
                house["Name"] = "Eric"
                house["HairColor"] = "black"
                break

    # Clue 13: The person who loves science fiction books is Arnold.
    for house in houses:
        if house["Name"] == "Arnold":
            house["BookGenre"] = "science fiction"
            break
    else:
        for house in houses:
            if house["BookGenre"] is None:
                house["BookGenre"] = "science fiction"
                house["Name"] = "Arnold"
                break

    # Determine remaining attributes
    # Assign remaining house styles
    remaining_styles = ["ranch", "victorian"]
    for house in houses:
        if house["HouseStyle"] is None:
            for style in remaining_styles:
                if style not in [h["HouseStyle"] for h in houses]:
                    house["HouseStyle"] = style
                    remaining_styles.remove(style)
                    break

    # Assign remaining hair colors
    remaining_colors = ["blonde"]
    for house in houses:
        if house["HairColor"] is None:
            for color in remaining_colors:
                if color not in [h["HairColor"] for h in houses]:
                    house["HairColor"] = color
                    remaining_colors.remove(color)
                    break

    # Assign remaining children
    remaining_children = ["Fred"]
    for house in houses:
        if house["Children"] is None:
            for child in remaining_children:
                if child not in [h["Children"] for h in houses]:
                    house["Children"] = child
                    remaining_children.remove(child)
                    break

    # Assign remaining book genres
    remaining_genres = ["mystery"]
    for house in houses:
        if house["BookGenre"] is None:
            for genre in remaining_genres:
                if genre not in [h["BookGenre"] for h in houses]:
                    house["BookGenre"] = genre
                    remaining_genres.remove(genre)
                    break

    # Assign remaining names
    remaining_names = ["Eric"]
    for house in houses:
        if house["Name"] is None:
            for name in remaining_names:
                if name not in [h["Name"] for h in houses]:
                    house["Name"] = name
                    remaining_names.remove(name)
                    break

    # Ensure clue 5 is satisfied
    red_hair_index = next(i for i, house in enumerate(houses) if house["HairColor"] == "red")
    ranch_index = next(i for i, house in enumerate(houses) if house["HouseStyle"] == "ranch")
    assert ranch_index > red_hair_index, "Clue 5 is not satisfied"

    # Format the solution as JSON
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
            "rows": [list(house.values()) for house in houses]
        }
    }

    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())