#!/usr/bin/env python3
import json

# Global domain lists
NAMES = {"Arnold", "Carol", "Peter", "Eric", "Bob", "Alice"}
HOUSE_STYLES = {"ranch", "colonial", "modern", "craftsman", "mediterranean", "victorian"}
FOODS = {"pizza", "stew", "spaghetti", "grilled cheese", "stir fry", "soup"}
VACATIONS = {"cultural", "cruise", "mountain", "camping", "city", "beach"}
HEIGHTS = {"average", "very tall", "very short", "short", "tall", "super tall"}
CIGARS = {"yellow monster", "prince", "dunhill", "pall mall", "blue master", "blends"}

# This function checks the internal self-consistency of a candidate house assignment.
def candidate_valid(c):
    # Tie: stir fry <-> colonial & average 
    if c["Food"] == "stir fry":
        if c["HouseStyle"] != "colonial":
            return False
        if c["Height"] != "average":
            return False
    if c["HouseStyle"] == "colonial" and c["Food"] != "stir fry":
        return False
    if c["Height"] == "average" and c["Food"] != "stir fry":
        return False

    # Tie: spaghetti <-> victorian
    if c["Food"] == "spaghetti" and c["HouseStyle"] != "victorian":
        return False
    if c["HouseStyle"] == "victorian" and c["Food"] != "spaghetti":
        return False

    # Tie: beach <-> ranch and tall <-> beach
    if c["Vacation"] == "beach" and c["HouseStyle"] != "ranch":
        return False
    if c["HouseStyle"] == "ranch" and c["Vacation"] != "beach":
        return False
    if c["Height"] == "tall" and c["Vacation"] != "beach":
        return False
    if c["Vacation"] == "beach" and c["Height"] != "tall":
        return False

    # Tie: mountain <-> (yellow monster & very tall)
    if c["Vacation"] == "mountain":
        if c["Cigar"] != "yellow monster":
            return False
        if c["Height"] != "very tall":
            return False
    if c["Cigar"] == "yellow monster" and c["Vacation"] != "mountain":
        return False
    if c["Height"] == "very tall" and c["Vacation"] != "mountain":
        return False

    # Tie: cultural <-> pizza
    if c["Vacation"] == "cultural" and c["Food"] != "pizza":
        return False
    if c["Food"] == "pizza" and c["Vacation"] != "cultural":
        return False

    # Tie: ranch <-> blue master
    if c["HouseStyle"] == "ranch" and c["Cigar"] != "blue master":
        return False
    if c["Cigar"] == "blue master" and c["HouseStyle"] != "ranch":
        return False

    # Tie: Arnold <-> stew
    if c["Name"] == "Arnold" and c["Food"] != "stew":
        return False
    if c["Food"] == "stew" and c["Name"] != "Arnold":
        return False

    # Clue: Alice loves spaghetti 
    if c["Name"] == "Alice" and c["Food"] != "spaghetti":
        return False

    return True

# This function checks inter-house constraints on the partial (or complete) assignment.
def check_partial(assignment):
    n = len(assignment)
    # Constraint 1: Alice is in the fifth house (index 4)
    if n > 4:
        if assignment[4]["Name"] != "Alice":
            return False
    # Constraint 9: Eric is in the fourth house (index 3)
    if n > 3:
        if assignment[3]["Name"] != "Eric":
            return False
    # Constraint 6: Craftsman is not in the third house (index 2)
    if n > 2:
        if assignment[2]["HouseStyle"] == "craftsman":
            return False
    # Constraint 5: There is one house between the person with average height and Peter.
    idx_avg = None
    idx_peter = None
    for i, house in enumerate(assignment):
        if house["Height"] == "average":
            idx_avg = i
        if house["Name"] == "Peter":
            idx_peter = i
    if idx_avg is not None and idx_peter is not None:
        if abs(idx_avg - idx_peter) != 2:
            return False
    # Constraint 10: One house between the colonial house and the camping vacation.
    idx_colonial = None
    idx_camping = None
    for i, house in enumerate(assignment):
        if house["HouseStyle"] == "colonial":
            idx_colonial = i
        if house["Vacation"] == "camping":
            idx_camping = i
    if idx_colonial is not None and idx_camping is not None:
        if abs(idx_colonial - idx_camping) != 2:
            return False
    # Constraint 13: Mountain vacation must be next to the Dunhill smoker.
    for i, house in enumerate(assignment):
        if house["Vacation"] == "mountain":
            # If house is in the middle and both neighbors are assigned, check at least one is Dunhill.
            if i > 0 and i < n - 1:
                left = assignment[i-1].get("Cigar")
                right = assignment[i+1].get("Cigar")
                if (left is not None and right is not None):
                    if left != "dunhill" and right != "dunhill":
                        return False
            # For the first house, if right neighbor exists, check it.
            elif i == 0 and n > 1:
                if assignment[1].get("Cigar") is not None and assignment[1]["Cigar"] != "dunhill":
                    return False
            # For last house in a complete assignment (n==6), then left neighbor must be dunhill.
            elif i == n - 1 and n == 6 and assignment[i-1].get("Cigar") is not None:
                if assignment[i-1]["Cigar"] != "dunhill":
                    return False
    # Constraint 16: Tall person is to the left of the Victorian house.
    idx_tall = None
    idx_victorian = None
    for i, house in enumerate(assignment):
        if house["Height"] == "tall":
            idx_tall = i
        if house["HouseStyle"] == "victorian":
            idx_victorian = i
    if idx_tall is not None and idx_victorian is not None:
        if idx_tall >= idx_victorian:
            return False
    # Constraint 17: The stir fry lover is directly left of Bob.
    for i, house in enumerate(assignment):
        if house["Food"] == "stir fry":
            if i < n - 1:  # next house is assigned
                if assignment[i+1]["Name"] != "Bob":
                    return False
    # Constraint 18: Modern house is somewhere to the left of Alice.
    idx_modern = None
    idx_alice = None
    for i, house in enumerate(assignment):
        if house["HouseStyle"] == "modern":
            idx_modern = i
        if house["Name"] == "Alice":
            idx_alice = i
    if idx_modern is not None and idx_alice is not None:
        if idx_modern >= idx_alice:
            return False
    # Constraint 19: Craftsman house is to the left of the short person.
    idx_craftsman = None
    idx_short = None
    for i, house in enumerate(assignment):
        if house["HouseStyle"] == "craftsman":
            idx_craftsman = i
        if house["Height"] == "short":
            idx_short = i
    if idx_craftsman is not None and idx_short is not None:
        if idx_craftsman >= idx_short:
            return False
    # Constraint 20: Stir fry lover is somewhere to the left of the Prince smoker.
    idx_stir = None
    idx_prince = None
    for i, house in enumerate(assignment):
        if house["Food"] == "stir fry":
            idx_stir = i
        if house["Cigar"] == "prince":
            idx_prince = i
    if idx_stir is not None and idx_prince is not None:
        if idx_stir >= idx_prince:
            return False
    # Constraint 21: Two houses between grilled cheese lover and super tall person.
    idx_grilled = None
    idx_super = None
    for i, house in enumerate(assignment):
        if house["Food"] == "grilled cheese":
            idx_grilled = i
        if house["Height"] == "super tall":
            idx_super = i
    if idx_grilled is not None and idx_super is not None:
        if abs(idx_grilled - idx_super) != 3:
            return False
    # Constraint 23: Blends smoker is directly left of Blue Master smoker.
    for i, house in enumerate(assignment):
        if house["Cigar"] == "blends":
            if i < n - 1:
                if assignment[i+1]["Cigar"] != "blue master":
                    return False
    # Constraint 25: Pizza lover is to the left of the person who likes cruises.
    idx_pizza = None
    idx_cruise = None
    for i, house in enumerate(assignment):
        if house["Food"] == "pizza":
            idx_pizza = i
        if house["Vacation"] == "cruise":
            idx_cruise = i
    if idx_pizza is not None and idx_cruise is not None:
        if idx_pizza >= idx_cruise:
            return False

    return True

# Backtracking search: assign houses sequentially (indices 0..5 correspond to houses 1..6).
def backtrack(index, assignment, av_names, av_styles, av_foods, av_vacations, av_heights, av_cigars):
    if index == 6:
        if check_partial(assignment):
            return assignment
        return None

    # Iterate over all candidate tuples from the available sets.
    for name in av_names:
        for style in av_styles:
            for food in av_foods:
                for vac in av_vacations:
                    for height in av_heights:
                        for cigar in av_cigars:
                            candidate = {
                                "Name": name,
                                "HouseStyle": style,
                                "Food": food,
                                "Vacation": vac,
                                "Height": height,
                                "Cigar": cigar
                            }
                            # Enforce fixed positions:
                            if index == 3 and candidate["Name"] != "Eric":
                                continue
                            if index == 4:
                                if candidate["Name"] != "Alice":
                                    continue
                                if candidate["HouseStyle"] != "victorian":
                                    continue
                                if candidate["Food"] != "spaghetti":
                                    continue
                            # Check candidate's internal consistency.
                            if not candidate_valid(candidate):
                                continue

                            new_assignment = assignment + [candidate]
                            if not check_partial(new_assignment):
                                continue

                            new_av_names = av_names.copy()
                            new_av_names.remove(name)
                            new_av_styles = av_styles.copy()
                            new_av_styles.remove(style)
                            new_av_foods = av_foods.copy()
                            new_av_foods.remove(food)
                            new_av_vacations = av_vacations.copy()
                            new_av_vacations.remove(vac)
                            new_av_heights = av_heights.copy()
                            new_av_heights.remove(height)
                            new_av_cigars = av_cigars.copy()
                            new_av_cigars.remove(cigar)

                            result = backtrack(index + 1, new_assignment, new_av_names, new_av_styles, new_av_foods, new_av_vacations, new_av_heights, new_av_cigars)
                            if result is not None:
                                return result
    return None

def main():
    solution = backtrack(0, [], NAMES, HOUSE_STYLES, FOODS, VACATIONS, HEIGHTS, CIGARS)
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"], "rows": []}}
    else:
        rows = []
        # Houses are numbered 1..6.
        for i, house in enumerate(solution):
            row = [
                str(i + 1),
                house["Name"],
                house["HouseStyle"],
                house["Food"],
                house["Vacation"],
                house["Height"],
                house["Cigar"]
            ]
            rows.append(row)
        output = {"solution": {"header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"], "rows": rows}}
    print(json.dumps(output))

if __name__ == "__main__":
    main()