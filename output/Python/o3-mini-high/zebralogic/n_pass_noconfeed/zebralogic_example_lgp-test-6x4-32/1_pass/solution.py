#!/usr/bin/env python3
import json
from itertools import product

# Global lists for domains
NAMES = ["Eric", "Alice", "Arnold", "Carol", "Peter", "Bob"]
HOUSE_STYLES = ["mediterranean", "modern", "craftsman", "ranch", "colonial", "victorian"]
MUSIC_GENRES = ["country", "hip hop", "pop", "jazz", "classical", "rock"]
HOBBIES = ["cooking", "painting", "photography", "woodworking", "gardening", "knitting"]

def check_constraints(assignment, complete=False):
    n = len(assignment)
    
    # Constraint 11: The person who loves country music is in the first house.
    if n > 0:
        if assignment[0]["MusicGenre"] != "country":
            return False

    # Constraint 15: Bob is in the third house.
    if n > 2:
        if assignment[2]["Name"] != "Bob":
            return False

    # Check individual house (if already assigned) for fixed associations:
    for i, house in enumerate(assignment):
        name = house["Name"]
        style = house["HouseStyle"]
        music = house["MusicGenre"]
        hobby = house["Hobby"]

        # Constraint 7: Carol is the person who loves hip-hop music.
        if name == "Carol":
            if music != "hip hop":
                return False
            if style != "mediterranean":
                return False

        # Constraint 9 & 14: The person in a ranch-style home is Eric, and he enjoys gardening.
        if name == "Eric":
            if style != "ranch":
                return False
            if hobby != "gardening":
                return False

        # Constraint 8: The person in a Craftsman-style house is Arnold.
        if name == "Arnold":
            if style != "craftsman":
                return False

        # Constraint 13: Alice is the photography enthusiast.
        if name == "Alice":
            if hobby != "photography":
                return False

        # Constraint: Mediterranean style <=> hip hop music.
        if style == "mediterranean" and music != "hip hop":
            return False
        if music == "hip hop" and style != "mediterranean":
            return False

        # Constraint: Ranch-style home must be Eric.
        if style == "ranch" and name != "Eric":
            return False

        # Constraint: Craftsman-style home must be Arnold.
        if style == "craftsman" and name != "Arnold":
            return False

        # Constraint 10: The woodworking hobbyist is in the Victorian house.
        if style == "victorian" and hobby != "woodworking":
            return False
        if hobby == "woodworking" and style != "victorian":
            return False

    # Constraint 1: The person who loves rock music is in the fifth house.
    if n > 4:
        if assignment[4]["MusicGenre"] != "rock":
            return False

    # Constraint 5: The person who loves jazz is directly left of Eric.
    for i, house in enumerate(assignment):
        if house["Name"] == "Eric":
            if i == 0:
                return False
            # The immediate left house must have jazz.
            if assignment[i - 1]["MusicGenre"] != "jazz":
                return False

    # Constraint 2: The person who loves classical music and the woodworking hobbyist are next to each other.
    # Check for houses with classical music:
    for i, house in enumerate(assignment):
        if house["MusicGenre"] == "classical":
            # Only check neighbor if we have at least one neighbor assigned.
            neighbors = []
            if i - 1 >= 0:
                neighbors.append(i - 1)
            if i + 1 < n:
                neighbors.append(i + 1)
            # If we are at a boundary in a complete solution, require the one neighbor check.
            if complete or (i != n - 1):
                if neighbors:
                    if not any(assignment[j]["Hobby"] == "woodworking" for j in neighbors):
                        return False

    # Also check: for any house with woodworking, one of its neighbors must have classical music.
    for i, house in enumerate(assignment):
        if house["Hobby"] == "woodworking":
            neighbors = []
            if i - 1 >= 0:
                neighbors.append(i - 1)
            if i + 1 < n:
                neighbors.append(i + 1)
            if complete or (i != n - 1):
                if neighbors:
                    if not any(assignment[j]["MusicGenre"] == "classical" for j in neighbors):
                        return False

    # Constraint 4: There are two houses between Arnold and the person residing in a Victorian house.
    indices_arnold = [i for i, house in enumerate(assignment) if house["Name"] == "Arnold"]
    indices_victorian = [i for i, house in enumerate(assignment) if house["HouseStyle"] == "victorian"]
    if indices_arnold and indices_victorian:
        # Since there is exactly one Arnold and one Victorian in a complete solution,
        # when both are present, their positions must differ by 3.
        if len(indices_arnold) == 1 and len(indices_victorian) == 1:
            if abs(indices_arnold[0] - indices_victorian[0]) != 3:
                return False

    # Constraint 6: The person who loves hip-hop music is somewhere to the left of the person who enjoys knitting.
    index_hiphop = None
    index_knitting = None
    for i, house in enumerate(assignment):
        if house["MusicGenre"] == "hip hop":
            index_hiphop = i
        if house["Hobby"] == "knitting":
            index_knitting = i
    if index_hiphop is not None and index_knitting is not None:
        if index_hiphop >= index_knitting:
            return False

    # Constraint 12: There is one house between the person who paints and the person living in a colonial-style house.
    index_painting = None
    index_colonial = None
    for i, house in enumerate(assignment):
        if house["Hobby"] == "painting":
            index_painting = i
        if house["HouseStyle"] == "colonial":
            index_colonial = i
    if index_painting is not None and index_colonial is not None:
        if abs(index_painting - index_colonial) != 2:
            return False

    return True

def backtrack(i, names_rem, styles_rem, music_rem, hobbies_rem, assignment):
    if i == 6:
        # Complete assignment reached. Check full constraints.
        if check_constraints(assignment, complete=True):
            return assignment
        else:
            return None

    # Loop over all possible choices for the current house from remaining domain values.
    for name in names_rem:
        for style in styles_rem:
            for music in music_rem:
                for hobby in hobbies_rem:
                    house = {
                        "House": str(i + 1),
                        "Name": name,
                        "HouseStyle": style,
                        "MusicGenre": music,
                        "Hobby": hobby
                    }
                    assignment.append(house)
                    
                    # Prepare new remaining lists
                    new_names = names_rem.copy()
                    new_names.remove(name)
                    new_styles = styles_rem.copy()
                    new_styles.remove(style)
                    new_music = music_rem.copy()
                    new_music.remove(music)
                    new_hobbies = hobbies_rem.copy()
                    new_hobbies.remove(hobby)
                    
                    # Check constraints for the partial assignment.
                    if check_constraints(assignment, complete=False):
                        result = backtrack(i + 1, new_names, new_styles, new_music, new_hobbies, assignment)
                        if result is not None:
                            return result
                    # Backtrack
                    assignment.pop()
    return None

def solve_puzzle():
    solution = backtrack(0, NAMES, HOUSE_STYLES, MUSIC_GENRES, HOBBIES, [])
    return solution

def main():
    sol = solve_puzzle()
    if sol is None:
        output = {"solution": {"header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"], "rows": []}}
    else:
        rows = []
        # Ensure the solution is ordered from house 1 to 6.
        sol_sorted = sorted(sol, key=lambda x: int(x["House"]))
        for house in sol_sorted:
            rows.append([house["House"], house["Name"], house["HouseStyle"], house["MusicGenre"], house["Hobby"]])
        output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
                "rows": rows
            }
        }
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()