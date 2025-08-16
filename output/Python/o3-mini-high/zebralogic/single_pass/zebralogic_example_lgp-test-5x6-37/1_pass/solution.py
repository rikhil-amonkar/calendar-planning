#!/usr/bin/env python3
import json

# Domains for each attribute
NAMES = {"Bob", "Arnold", "Alice", "Peter", "Eric"}
HOBBIES = {"cooking", "gardening", "painting", "photography", "knitting"}
SPORTS = {"swimming", "tennis", "soccer", "baseball", "basketball"}
HOUSE_STYLES = {"ranch", "craftsman", "victorian", "modern", "colonial"}
CHILDREN = {"Timothy", "Samantha", "Bella", "Meredith", "Fred"}
HEIGHTS = {"average", "very tall", "very short", "short", "tall"}

# This function checks if the partial (or complete) assignment "solution" (a list of house dicts)
# is consistent with all the clues.
def consistent(solution):
    # solution is a list where index 0 is house 1, index 1 is house 2, etc.
    houses = solution
    n = len(houses)
    
    for i, house in enumerate(houses):
        # Clue 1: The person with average height has child Meredith.
        if house.get("Height") == "average":
            if house.get("Children") is not None and house.get("Children") != "Meredith":
                return False
        if house.get("Children") == "Meredith":
            if house.get("Height") is not None and house.get("Height") != "average":
                return False
        
        # Clue 2: The person who is tall is in the second house.
        if i == 1:
            if house.get("Height") != "tall":
                return False
        else:
            if house.get("Height") == "tall":
                return False
        
        # Clue 3: Peter is directly left of the person in a Victorian house.
        if house.get("Name") == "Peter":
            if i+1 < n:
                next_style = houses[i+1].get("HouseStyle")
                if next_style is not None and next_style != "victorian":
                    return False
        if house.get("HouseStyle") == "victorian":
            # Victorian house must be house 5 (index 4). Also if there is a house immediately to its left, that house must be Peter.
            if i != 4:
                return False
            if i > 0:
                prev_name = houses[i-1].get("Name")
                if prev_name is not None and prev_name != "Peter":
                    return False

        # Clue 4: Alice is the person who is tall.
        if house.get("Name") == "Alice":
            if house.get("Height") is not None and house.get("Height") != "tall":
                return False
        if house.get("Height") == "tall":
            if house.get("Name") is not None and house.get("Name") != "Alice":
                return False

        # Clue 5: The person who loves baseball is the person who is very tall.
        if house.get("FavoriteSport") == "baseball":
            if house.get("Height") is not None and house.get("Height") != "very tall":
                return False
        if house.get("Height") == "very tall":
            if house.get("FavoriteSport") is not None and house.get("FavoriteSport") != "baseball":
                return False

        # Clue 7: Bob is the person who paints.
        if house.get("Name") == "Bob":
            if house.get("Hobby") is not None and house.get("Hobby") != "painting":
                return False
        if house.get("Hobby") == "painting":
            if house.get("Name") is not None and house.get("Name") != "Bob":
                return False

        # Clue 8: The person who enjoys gardening is in the second house.
        if i == 1:
            if house.get("Hobby") != "gardening":
                return False

        # Clue 10: The person who loves tennis has child Samantha.
        if house.get("FavoriteSport") == "tennis":
            if house.get("Children") is not None and house.get("Children") != "Samantha":
                return False
        if house.get("Children") == "Samantha":
            if house.get("FavoriteSport") is not None and house.get("FavoriteSport") != "tennis":
                return False

        # Clue 11: The person who loves soccer is not in the first house.
        if i == 0:
            if house.get("FavoriteSport") == "soccer":
                return False

        # Clue 12: The person whose child is Samantha lives in a modern-style house.
        if house.get("Children") == "Samantha":
            if house.get("HouseStyle") is not None and house.get("HouseStyle") != "modern":
                return False
        if house.get("HouseStyle") == "modern":
            if house.get("Children") is not None and house.get("Children") != "Samantha":
                return False

        # Clue 13: The person in a Craftsman-style house has average height.
        if house.get("HouseStyle") == "craftsman":
            if house.get("Height") is not None and house.get("Height") != "average":
                return False
        if house.get("Height") == "average":
            if house.get("HouseStyle") is not None and house.get("HouseStyle") != "craftsman":
                return False

        # Clue 14: The person whose child is Fred lives in a Victorian house.
        if house.get("Children") == "Fred":
            if house.get("HouseStyle") is not None and house.get("HouseStyle") != "victorian":
                return False
        if house.get("HouseStyle") == "victorian":
            if house.get("Children") is not None and house.get("Children") != "Fred":
                return False

        # Clue 15: The person who is short loves basketball.
        if house.get("Height") == "short":
            if house.get("FavoriteSport") is not None and house.get("FavoriteSport") != "basketball":
                return False
        if house.get("FavoriteSport") == "basketball":
            if house.get("Height") is not None and house.get("Height") != "short":
                return False

        # Clue 16: Peter is the person who is very tall.
        if house.get("Name") == "Peter":
            if house.get("Height") is not None and house.get("Height") != "very tall":
                return False
        if house.get("Height") == "very tall":
            if house.get("Name") is not None and house.get("Name") != "Peter":
                return False

        # Clue 19: The person in a modern-style house loves cooking.
        if house.get("HouseStyle") == "modern":
            if house.get("Hobby") is not None and house.get("Hobby") != "cooking":
                return False
        if house.get("Hobby") == "cooking":
            if house.get("HouseStyle") is not None and house.get("HouseStyle") != "modern":
                return False

    # Now check inter-house (relative) constraints.
    
    # Clue 6: The house with child Meredith and the house with child Timothy are neighbors.
    indices_meredith = [idx for idx, h in enumerate(houses) if h.get("Children") == "Meredith"]
    indices_timothy = [idx for idx, h in enumerate(houses) if h.get("Children") == "Timothy"]
    if indices_meredith and indices_timothy:
        valid_pair = False
        for m in indices_meredith:
            for t in indices_timothy:
                if abs(m - t) == 1:
                    valid_pair = True
        if not valid_pair:
            return False

    # Clue 9: The person who is very short is somewhere to the right of Eric.
    indices_eric = [idx for idx, h in enumerate(houses) if h.get("Name") == "Eric"]
    indices_very_short = [idx for idx, h in enumerate(houses) if h.get("Height") == "very short"]
    if indices_eric:
        for e in indices_eric:
            # If Eric is in the last house, then there is no house to its right.
            if e == len(houses) - 1 and len(houses) == 5:
                return False
            # If any assigned "very short" is not to the right of Eric, fail.
            for vs in indices_very_short:
                if vs <= e:
                    return False

    # Clue 17: The house with a ranch-style home is somewhere to the left of the house that loves cooking.
    indices_ranch = [idx for idx, h in enumerate(houses) if h.get("HouseStyle") == "ranch"]
    indices_cooking = [idx for idx, h in enumerate(houses) if h.get("Hobby") == "cooking"]
    if indices_ranch and indices_cooking:
        valid_pair = False
        for r in indices_ranch:
            for c in indices_cooking:
                if r < c:
                    valid_pair = True
        if not valid_pair:
            return False

    # Clue 18: The person who enjoys knitting is next to the person who enjoys gardening.
    indices_knitting = [idx for idx, h in enumerate(houses) if h.get("Hobby") == "knitting"]
    indices_gardening = [idx for idx, h in enumerate(houses) if h.get("Hobby") == "gardening"]
    if indices_knitting and indices_gardening:
        valid_pair = False
        for k in indices_knitting:
            for g in indices_gardening:
                if abs(k - g) == 1:
                    valid_pair = True
        if not valid_pair:
            return False

    return True

# Backtracking search:
def backtrack(i, solution, rem_names, rem_hobbies, rem_sports, rem_styles, rem_children, rem_heights):
    if i == 5:
        if consistent(solution):
            return solution
        else:
            return None

    # For house number i (0-indexed), iterate over all combinations from the remaining domains.
    for name in list(rem_names):
        # Forced conditions:
        if i == 1 and name != "Alice":
            continue
        if i == 3 and name != "Peter":
            continue

        for hobby in list(rem_hobbies):
            if i == 1 and hobby != "gardening":
                continue

            for sport in list(rem_sports):
                if i == 3 and sport != "baseball":
                    continue
                if i == 0 and sport == "soccer":
                    continue

                for style in list(rem_styles):
                    if i == 4 and style != "victorian":
                        continue
                    if i != 4 and style == "victorian":
                        continue

                    for child in list(rem_children):
                        if i == 4 and child != "Fred":
                            continue

                        for height in list(rem_heights):
                            if i == 1 and height != "tall":
                                continue
                            if i != 1 and height == "tall":
                                continue

                            candidate = {
                                "Name": name,
                                "Hobby": hobby,
                                "FavoriteSport": sport,
                                "HouseStyle": style,
                                "Children": child,
                                "Height": height
                            }
                            new_solution = solution + [candidate]
                            if not consistent(new_solution):
                                continue

                            new_rem_names = set(rem_names)
                            new_rem_names.remove(name)
                            new_rem_hobbies = set(rem_hobbies)
                            new_rem_hobbies.remove(hobby)
                            new_rem_sports = set(rem_sports)
                            new_rem_sports.remove(sport)
                            new_rem_styles = set(rem_styles)
                            new_rem_styles.remove(style)
                            new_rem_children = set(rem_children)
                            new_rem_children.remove(child)
                            new_rem_heights = set(rem_heights)
                            new_rem_heights.remove(height)

                            result = backtrack(i+1, new_solution, new_rem_names, new_rem_hobbies, new_rem_sports, new_rem_styles, new_rem_children, new_rem_heights)
                            if result is not None:
                                return result
    return None

def main():
    solution = backtrack(0, [], NAMES, HOBBIES, SPORTS, HOUSE_STYLES, CHILDREN, HEIGHTS)
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"], "rows": []}}
    else:
        # Prepare rows in house order (house numbers 1 to 5)
        rows = []
        for idx, house in enumerate(solution):
            row = [
                str(idx + 1),
                house["Name"],
                house["Hobby"],
                house["FavoriteSport"],
                house["HouseStyle"],
                house["Children"],
                house["Height"]
            ]
            rows.append(row)
        output = {
            "solution": {
                "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
                "rows": rows
            }
        }
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()