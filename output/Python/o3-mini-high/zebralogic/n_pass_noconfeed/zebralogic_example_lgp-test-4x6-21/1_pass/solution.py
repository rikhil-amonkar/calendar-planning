import itertools
import json

def main():
    names_all = ["Peter", "Arnold", "Alice", "Eric"]
    styles_all = ["craftsman", "colonial", "ranch", "victorian"]
    colors_all = ["red", "yellow", "green", "white"]
    hobbies_all = ["photography", "painting", "cooking", "gardening"]
    pets_all = ["dog", "fish", "bird", "cat"]
    
    # Mapping from color to flower
    flower_by_color = {
        "red": "roses",
        "yellow": "daffodils",
        "white": "carnations",
        "green": "lilies"
    }
    
    solution = None
    
    # Iterate over possible assignments for names
    for names in itertools.permutations(names_all):
        # Constraint: House 2 (index 1) must be Arnold
        if names[1] != "Arnold":
            continue
        # Constraint: Peter must be in a house to the left of the red house.
        # Since red cannot be in house1, Peter almost certainly must be house1.
        if names[0] != "Peter":
            continue
            
        # Iterate over possible assignments for house styles
        for styles in itertools.permutations(styles_all):
            # Constraint: Craftsman is in the second house (index 1)
            if styles[1] != "craftsman":
                continue
            # Constraint: Craftsman should only be in house2.
            if any(styles[i] == "craftsman" for i in range(4) if i != 1):
                continue
            # Constraint: Eric must be in a Victorian house.
            index_eric = names.index("Eric")
            if styles[index_eric] != "victorian":
                continue

            # Iterate over possible assignments for colors
            for colors in itertools.permutations(colors_all):
                valid = True
                # For each house, if the style is colonial then its color must be red
                # And conversely, if the color is red, the house must be colonial.
                for i in range(4):
                    if styles[i] == "colonial" and colors[i] != "red":
                        valid = False
                        break
                    if colors[i] == "red" and styles[i] != "colonial":
                        valid = False
                        break
                if not valid:
                    continue
                # Constraint: The house with daffodils (yellow) is not the fourth house.
                if colors[3] == "yellow":
                    continue
                # Constraint: The red house (rose bouquet) is to the right of Peter.
                try:
                    index_red = colors.index("red")
                except ValueError:
                    continue
                if index_red <= names.index("Peter"):
                    continue
                    
                # Iterate over possible assignments for hobbies
                for hobbies in itertools.permutations(hobbies_all):
                    # Constraint: The person who loves cooking must be to the right of the red house.
                    try:
                        index_cooking = hobbies.index("cooking")
                    except ValueError:
                        continue
                    if index_cooking <= index_red:
                        continue
                    # Constraint: The person who enjoys gardening is to the left of the person who loves white.
                    try:
                        index_gardening = hobbies.index("gardening")
                        index_white = colors.index("white")
                    except ValueError:
                        continue
                    if index_gardening >= index_white:
                        continue
                        
                    # Iterate over possible assignments for pets
                    for pets in itertools.permutations(pets_all):
                        valid_pets = True
                        # Constraint: The photography enthusiast is the person who owns a dog.
                        for i in range(4):
                            if hobbies[i] == "photography" and pets[i] != "dog":
                                valid_pets = False
                                break
                        if not valid_pets:
                            continue
                        # Constraint: The person with white color must have fish.
                        for i in range(4):
                            if colors[i] == "white" and pets[i] != "fish":
                                valid_pets = False
                                break
                        if not valid_pets:
                            continue
                        # Constraint: The person who has a cat is Eric.
                        for i in range(4):
                            if names[i] == "Eric" and pets[i] != "cat":
                                valid_pets = False
                                break
                        if not valid_pets:
                            continue
                        
                        # All constraints satisfied, record the solution.
                        houses = []
                        for i in range(4):
                            house = {
                                "House": str(i + 1),
                                "Name": names[i],
                                "Flower": flower_by_color[colors[i]],
                                "Hobby": hobbies[i],
                                "Pet": pets[i],
                                "Color": colors[i],
                                "HouseStyle": styles[i]
                            }
                            houses.append(house)
                        
                        solution = houses
                        break
                    if solution is not None:
                        break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    if solution is not None:
        # Arrange the solution in the required JSON structure.
        output = {
            "solution": {
                "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
                "rows": [
                    [
                        house["House"],
                        house["Name"],
                        house["Flower"],
                        house["Hobby"],
                        house["Pet"],
                        house["Color"],
                        house["HouseStyle"]
                    ]
                    for house in sorted(solution, key=lambda h: int(h["House"]))
                ]
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()