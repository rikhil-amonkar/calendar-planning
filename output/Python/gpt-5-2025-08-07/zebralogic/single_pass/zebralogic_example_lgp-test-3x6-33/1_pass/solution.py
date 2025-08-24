import itertools
import json

def solve():
    houses = [0, 1, 2]  # indices for houses 1,2,3
    categories = ["Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"]
    values = {
        "Name": ["Arnold", "Eric", "Peter"],
        "Flower": ["carnations", "lilies", "daffodils"],
        "HairColor": ["black", "brown", "blonde"],
        "FavoriteSport": ["soccer", "basketball", "tennis"],
        "HouseStyle": ["colonial", "ranch", "victorian"],
        "Pet": ["fish", "dog", "cat"],
    }

    # Helper to check constraints
    def get_pos(assignment, category, value):
        if category not in assignment:
            return None
        return assignment[category].index(value)

    def is_consistent(assignment):
        # Clue 2: Blonde hair is in the second house (index 1)
        p = get_pos(assignment, "HairColor", "blonde")
        if p is not None and p != 1:
            return False

        # Clue 3: Daffodils = Blonde hair
        p1 = get_pos(assignment, "Flower", "daffodils")
        p2 = get_pos(assignment, "HairColor", "blonde")
        if p1 is not None and p2 is not None and p1 != p2:
            return False

        # Since HairColor(blonde)=1, Flower(daffodils)=1 as well if Flower assigned
        if p1 is not None and p1 != 1:
            return False

        # Clue 4: Peter = Basketball
        p1 = get_pos(assignment, "Name", "Peter")
        p2 = get_pos(assignment, "FavoriteSport", "basketball")
        if p1 is not None and p2 is not None and p1 != p2:
            return False

        # Clue 6: Dog = Basketball
        p1 = get_pos(assignment, "Pet", "dog")
        p2 = get_pos(assignment, "FavoriteSport", "basketball")
        if p1 is not None and p2 is not None and p1 != p2:
            return False

        # Clue 1: Cat = Soccer
        p1 = get_pos(assignment, "Pet", "cat")
        p2 = get_pos(assignment, "FavoriteSport", "soccer")
        if p1 is not None and p2 is not None and p1 != p2:
            return False

        # Clue 8: Soccer is in the third house (index 2)
        p = get_pos(assignment, "FavoriteSport", "soccer")
        if p is not None and p != 2:
            return False

        # Clue 10: Colonial is in the third house (index 2)
        p = get_pos(assignment, "HouseStyle", "colonial")
        if p is not None and p != 2:
            return False

        # Clue 5: Arnold is directly left of Ranch
        pa = get_pos(assignment, "Name", "Arnold")
        pr = get_pos(assignment, "HouseStyle", "ranch")
        if pr is not None and pr == 0:
            return False  # Ranch can't be at house 1 due to "left of"
        if pa is not None and pa == 2:
            return False  # Arnold can't be at house 3 due to "left of"
        if pa is not None and pr is not None and not (pa + 1 == pr):
            return False

        # Clue 7: Carnations is directly left of Blonde
        pc = get_pos(assignment, "Flower", "carnations")
        pb = get_pos(assignment, "HairColor", "blonde")
        if pc is not None and pc == 2:
            return False  # can't be at house 3 due to "left of"
        if pb is not None and pb == 0:
            return False  # Blonde can't be at house 1 due to "left of"
        if pc is not None and pb is not None and not (pc + 1 == pb):
            return False

        # Clue 9: Arnold is somewhere to the left of Black hair
        pbk = get_pos(assignment, "HairColor", "black")
        if pbk is not None and pbk == 0:
            return False  # If black is at house 1, Arnold can't be left of it
        if pa is not None and pbk is not None and not (pa < pbk):
            return False

        return True

    # Backtracking search over permutations per category
    all_perms = {cat: list(itertools.permutations(values[cat])) for cat in categories}

    # Order categories for faster pruning
    order = ["FavoriteSport", "HairColor", "HouseStyle", "Name", "Flower", "Pet"]

    def backtrack(assignment, remaining):
        if not remaining:
            if is_consistent(assignment):
                return assignment
            return None
        cat = remaining[0]
        for perm in all_perms[cat]:
            assignment[cat] = list(perm)
            if is_consistent(assignment):
                result = backtrack(assignment, remaining[1:])
                if result is not None:
                    return result
            del assignment[cat]
        return None

    solution_assignment = backtrack({}, order)
    if solution_assignment is None:
        raise RuntimeError("No solution found")

    # Build output rows
    rows = []
    for i in range(3):
        row = [
            str(i + 1),
            solution_assignment["Name"][i],
            solution_assignment["Flower"][i],
            solution_assignment["HairColor"][i],
            solution_assignment["FavoriteSport"][i],
            solution_assignment["HouseStyle"][i],
            solution_assignment["Pet"][i],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve()