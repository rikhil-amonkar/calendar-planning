import json
from copy import deepcopy

def solve_puzzle():
    # Define houses and attributes
    houses = [1, 2, 3, 4, 5]
    categories = ["Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"]

    values = {
        "Name": ["Bob", "Arnold", "Alice", "Peter", "Eric"],
        "Hobby": ["cooking", "gardening", "painting", "photography", "knitting"],
        "FavoriteSport": ["swimming", "tennis", "soccer", "baseball", "basketball"],
        "HouseStyle": ["ranch", "craftsman", "victorian", "modern", "colonial"],
        "Children": ["Timothy", "Samantha", "Bella", "Meredith", "Fred"],
        "Height": ["average", "very tall", "very short", "short", "tall"],
    }

    # Grid: grid[category][house] = value or None (use 1-based indexing for houses)
    grid = {cat: [None] * (len(houses) + 1) for cat in categories}

    # Helper functions
    def house_of(cat, val):
        for h in houses:
            if grid[cat][h] == val:
                return h
        return None

    def is_adjacent(a, b):
        return abs(a - b) == 1

    def check_constraints():
        # Uniqueness: no duplicate values in a category
        for cat in categories:
            assigned = [v for v in grid[cat][1:] if v is not None]
            if len(assigned) != len(set(assigned)):
                return False

        # Clue 20: Victorian is in the fifth house (exclusive)
        # - If style at 5 assigned and not 'victorian' -> fail
        # - If 'victorian' appears in any house other than 5 -> fail
        if grid["HouseStyle"][5] is not None and grid["HouseStyle"][5] != "victorian":
            return False
        for h in houses:
            if grid["HouseStyle"][h] == "victorian" and h != 5:
                return False

        # Clue 2: The person who is tall is in the second house (exclusive)
        if grid["Height"][2] is not None and grid["Height"][2] != "tall":
            return False
        for h in houses:
            if grid["Height"][h] == "tall" and h != 2:
                return False

        # Clue 8: gardening is in the second house (exclusive)
        if grid["Hobby"][2] is not None and grid["Hobby"][2] != "gardening":
            return False
        for h in houses:
            if grid["Hobby"][h] == "gardening" and h != 2:
                return False

        # Clue 3: Peter is directly left of the person residing in a Victorian house
        h_peter = house_of("Name", "Peter")
        h_vic = house_of("HouseStyle", "victorian")
        if h_peter is not None and h_vic is not None:
            if h_peter + 1 != h_vic:
                return False
        # Peter cannot be in the last house under this clue
        if h_peter == 5:
            return False

        # Clue 4: Alice is tall
        h_alice = house_of("Name", "Alice")
        if h_alice is not None:
            if grid["Height"][h_alice] is not None and grid["Height"][h_alice] != "tall":
                return False
        h_tall = house_of("Height", "tall")
        if h_tall is not None:
            if grid["Name"][h_tall] is not None and grid["Name"][h_tall] != "Alice":
                return False

        # Clue 5: Baseball equals very tall
        for h in houses:
            if grid["FavoriteSport"][h] == "baseball":
                if grid["Height"][h] is not None and grid["Height"][h] != "very tall":
                    return False
            if grid["Height"][h] == "very tall":
                if grid["FavoriteSport"][h] is not None and grid["FavoriteSport"][h] != "baseball":
                    return False

        # Clue 6: Meredith and Timothy are next to each other
        h_mer = house_of("Children", "Meredith")
        h_tim = house_of("Children", "Timothy")
        if h_mer is not None and h_tim is not None:
            if not is_adjacent(h_mer, h_tim):
                return False

        # Clue 7: Bob paints
        h_bob = house_of("Name", "Bob")
        if h_bob is not None:
            if grid["Hobby"][h_bob] is not None and grid["Hobby"][h_bob] != "painting":
                return False
        h_paint = house_of("Hobby", "painting")
        if h_paint is not None:
            if grid["Name"][h_paint] is not None and grid["Name"][h_paint] != "Bob":
                return False

        # Clue 9: very short is somewhere to the right of Eric
        h_very_short = house_of("Height", "very short")
        h_eric = house_of("Name", "Eric")
        if h_very_short is not None and h_eric is not None:
            if not (h_very_short > h_eric):
                return False
        # Early impossibility: If Eric is in the last house
        if h_eric == 5:
            return False

        # Clue 10: tennis equals Samantha
        for h in houses:
            if grid["FavoriteSport"][h] == "tennis":
                if grid["Children"][h] is not None and grid["Children"][h] != "Samantha":
                    return False
            if grid["Children"][h] == "Samantha":
                if grid["FavoriteSport"][h] is not None and grid["FavoriteSport"][h] != "tennis":
                    return False

        # Clue 11: soccer is not in the first house
        if grid["FavoriteSport"][1] == "soccer":
            return False

        # Clue 12: Samantha equals modern
        for h in houses:
            if grid["Children"][h] == "Samantha":
                if grid["HouseStyle"][h] is not None and grid["HouseStyle"][h] != "modern":
                    return False
            if grid["HouseStyle"][h] == "modern":
                if grid["Children"][h] is not None and grid["Children"][h] != "Samantha":
                    return False

        # Clue 13: craftsman equals average
        for h in houses:
            if grid["HouseStyle"][h] == "craftsman":
                if grid["Height"][h] is not None and grid["Height"][h] != "average":
                    return False
            if grid["Height"][h] == "average":
                if grid["HouseStyle"][h] is not None and grid["HouseStyle"][h] != "craftsman":
                    return False

        # Clue 14: Fred equals Victorian
        for h in houses:
            if grid["Children"][h] == "Fred":
                if grid["HouseStyle"][h] is not None and grid["HouseStyle"][h] != "victorian":
                    return False
            if grid["HouseStyle"][h] == "victorian":
                if grid["Children"][h] is not None and grid["Children"][h] != "Fred":
                    return False

        # Clue 15: short equals basketball
        for h in houses:
            if grid["Height"][h] == "short":
                if grid["FavoriteSport"][h] is not None and grid["FavoriteSport"][h] != "basketball":
                    return False
            if grid["FavoriteSport"][h] == "basketball":
                if grid["Height"][h] is not None and grid["Height"][h] != "short":
                    return False

        # Clue 16: Peter is very tall
        for h in houses:
            if grid["Name"][h] == "Peter":
                if grid["Height"][h] is not None and grid["Height"][h] != "very tall":
                    return False
            if grid["Height"][h] == "very tall":
                if grid["Name"][h] is not None and grid["Name"][h] != "Peter":
                    return False

        # Clue 17: ranch is somewhere to the left of cooking
        h_ranch = house_of("HouseStyle", "ranch")
        h_cook = house_of("Hobby", "cooking")
        if h_ranch is not None and h_cook is not None:
            if not (h_ranch < h_cook):
                return False
        # Simple impossibilities: ranch cannot be at 5; cooking cannot be at 1
        if h_ranch == 5:
            return False
        if h_cook == 1:
            return False

        # Clue 18: knitting and gardening are next to each other
        h_knit = house_of("Hobby", "knitting")
        h_gard = house_of("Hobby", "gardening")
        if h_knit is not None and h_gard is not None:
            if not is_adjacent(h_knit, h_gard):
                return False
        # With gardening fixed to house 2, knitting cannot be at 4 or 5 unless unassigned
        # General adjacency check above suffices.

        # Clue 19: modern equals cooking
        for h in houses:
            if grid["HouseStyle"][h] == "modern":
                if grid["Hobby"][h] is not None and grid["Hobby"][h] != "cooking":
                    return False
            if grid["Hobby"][h] == "cooking":
                if grid["HouseStyle"][h] is not None and grid["HouseStyle"][h] != "modern":
                    return False

        # Clue 1: average equals Meredith
        for h in houses:
            if grid["Height"][h] == "average":
                if grid["Children"][h] is not None and grid["Children"][h] != "Meredith":
                    return False
            if grid["Children"][h] == "Meredith":
                if grid["Height"][h] is not None and grid["Height"][h] != "average":
                    return False

        return True

    # Pre-assignments derived directly from unambiguous clues to reduce search
    # Clue 20: Victorian at 5
    grid["HouseStyle"][5] = "victorian"
    # Clue 14: Fred is the person residing in a Victorian house -> at 5
    grid["Children"][5] = "Fred"
    # Clue 2: Tall is in the second house
    grid["Height"][2] = "tall"
    # Clue 8: Gardening is in the second house
    grid["Hobby"][2] = "gardening"
    # Clue 3 and 20 imply Peter is directly left of 5 -> at 4
    grid["Name"][4] = "Peter"
    # Clue 16: Peter is very tall
    grid["Height"][4] = "very tall"
    # Clue 5: Baseball equals very tall -> Peter loves baseball
    grid["FavoriteSport"][4] = "baseball"
    # Clue 4 with Clue 2: Alice is tall and tall is at 2 -> Alice at 2
    grid["Name"][2] = "Alice"

    # Used values tracking for each category
    used = {cat: set(v for v in grid[cat][1:] if v is not None) for cat in categories}

    # Backtracking with MRV
    cells = [(h, cat) for h in houses for cat in categories]

    def domain_for(h, cat):
        dom = []
        for val in values[cat]:
            if val in used[cat]:
                continue
            # Try assigning and test constraints
            grid[cat][h] = val
            used[cat].add(val)
            ok = check_constraints()
            # Revert
            used[cat].remove(val)
            grid[cat][h] = None
            if ok:
                dom.append(val)
        return dom

    def select_unassigned_var():
        # Minimum Remaining Values heuristic
        best = None
        best_domain = None
        for h in houses:
            for cat in categories:
                if grid[cat][h] is None:
                    dom = domain_for(h, cat)
                    if len(dom) == 0:
                        return (h, cat, dom)  # Early failure
                    if best is None or len(dom) < len(best_domain):
                        best = (h, cat)
                        best_domain = dom
                        if len(best_domain) == 1:
                            # optimal MRV found
                            return (best[0], best[1], best_domain)
        if best is None:
            return None
        return (best[0], best[1], best_domain)

    def is_complete():
        for cat in categories:
            for h in houses:
                if grid[cat][h] is None:
                    return False
        return True

    def backtrack():
        if is_complete():
            return True
        selection = select_unassigned_var()
        if selection is None:
            return False
        h, cat, dom = selection
        for val in dom:
            grid[cat][h] = val
            used[cat].add(val)
            if check_constraints():
                if backtrack():
                    return True
            used[cat].remove(val)
            grid[cat][h] = None
        return False

    success = check_constraints() and backtrack()
    if not success:
        raise RuntimeError("No solution found")

    # Build result rows
    header = ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"]
    rows = []
    for h in houses:
        row = [
            str(h),
            grid["Name"][h],
            grid["Hobby"][h],
            grid["FavoriteSport"][h],
            grid["HouseStyle"][h],
            grid["Children"][h],
            grid["Height"][h],
        ]
        rows.append(row)

    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))