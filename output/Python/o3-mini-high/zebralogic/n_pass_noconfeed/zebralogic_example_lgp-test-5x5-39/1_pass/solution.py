#!/usr/bin/env python3
import json
import itertools
import copy

# The full lists of attributes.
names_full = ["Alice", "Eric", "Bob", "Peter", "Arnold"]
birthdays_full = ["mar", "april", "sept", "feb", "jan"]
mothers_full = ["Holly", "Janelle", "Kailyn", "Penny", "Aniya"]
occupations_full = ["engineer", "doctor", "lawyer", "artist", "teacher"]
hair_full = ["red", "blonde", "black", "gray", "brown"]

# We set the house order: houses 1 to 5 correspond to indices 0..4.
# According to the clues:
# Clue 2: The person whose birthday is in February is in the first house.
# Clue 1: The person whose birthday is in March is in the fifth house.
# Clue 6+12: The person who is an artist (and has brown hair) is in the fourth house and that person’s birthday is January.
# For the remaining two houses, by deduction the birthdays become:
# House1: feb, House2: sept, House3: april, House4: jan, House5: mar.
# Also Clue 4 fixes: the person whose mother's name is Janelle is in the third house.
# Clue 10 and 17 fix that Alice (teacher with gray hair) has mother Kailyn; by deduction she is in House5.
# Also, as deduced, Bob must be in House4 (the artist).
#
# We create an initial list with fixed values.
def init_houses():
    houses = [{} for _ in range(5)]
    # Set the fixed birthdays.
    houses[0]["birthday"] = "feb"   # House 1
    houses[1]["birthday"] = "sept"  # House 2
    houses[2]["birthday"] = "april"  # House 3
    houses[3]["birthday"] = "jan"   # House 4
    houses[4]["birthday"] = "mar"   # House 5

    # Fixed by clues:
    # Clue 4: Third house has mother Janelle.
    houses[2]["mother"] = "Janelle"
    # Clue 6 and 5 and 12: Fourth house is the artist with brown hair and birthday jan.
    houses[3]["occupation"] = "artist"
    houses[3]["hair"] = "brown"
    # Clue 10, 17 and 9: Alice is teacher with gray hair and her mother is Kailyn.
    houses[4]["name"] = "Alice"
    houses[4]["occupation"] = "teacher"
    houses[4]["hair"] = "gray"
    houses[4]["mother"] = "Kailyn"
    return houses

# Check that the current partial assignment does not violate any constraints.
def check_constraints(houses):
    # Check individual house constraints.
    for house in houses:
        # Constraint: if a house has occupation "doctor", then the person is Eric (and vice versa).
        if "occupation" in house and house["occupation"] == "doctor":
            if "name" in house and house["name"] != "Eric":
                return False
        if "name" in house and house["name"] == "Eric":
            if "occupation" in house and house["occupation"] != "doctor":
                return False

        # Constraint: Peter is the person who has black hair and is a lawyer.
        if "name" in house and house["name"] == "Peter":
            if "hair" in house and house["hair"] != "black":
                return False
            if "occupation" in house and house["occupation"] != "lawyer":
                return False
        if "hair" in house and house["hair"] == "black":
            if "name" in house and house["name"] != "Peter":
                return False
            if "mother" in house and house["mother"] != "Holly":
                return False
        # Constraint: The person whose mother's name is Holly must have black hair.
        if "mother" in house and house["mother"] == "Holly":
            if "hair" in house and house["hair"] != "black":
                return False

        # Constraint: The person with gray hair is the teacher.
        if "hair" in house and house["hair"] == "gray":
            if "occupation" in house and house["occupation"] != "teacher":
                return False
        if "occupation" in house and house["occupation"] == "teacher":
            if "hair" in house and house["hair"] != "gray":
                return False

        # Constraint: Alice must have gray hair and her mother must be Kailyn.
        if "name" in house and house["name"] == "Alice":
            if "hair" in house and house["hair"] != "gray":
                return False
            if "mother" in house and house["mother"] != "Kailyn":
                return False
            if "occupation" in house and house["occupation"] != "teacher":
                return False

        # Constraint: Arnold must have blonde hair.
        if "name" in house and house["name"] == "Arnold":
            if "hair" in house and house["hair"] != "blonde":
                return False
        if "hair" in house and house["hair"] == "blonde":
            if "name" in house and house["name"] != "Arnold":
                return False

        # Constraint: If a house is artist, then hair must be brown. And vice versa.
        if "occupation" in house and house["occupation"] == "artist":
            if "hair" in house and house["hair"] != "brown":
                return False
        if "hair" in house and house["hair"] == "brown":
            if "birthday" in house and house["birthday"] != "jan":
                return False  # Clue 12: brown hair means birthday jan.
            if "occupation" in house and house["occupation"] != "artist":
                return False

    # Global uniqueness for attributes that have been assigned.
    for key in ["name", "mother", "occupation", "hair"]:
        seen = []
        for house in houses:
            if key in house:
                if house[key] in seen:
                    return False
                seen.append(house[key])

    # Global positional constraints.
    # Clue 7: The person whose mother's name is Penny is somewhere to the left of the person who has black hair.
    index_penny = None
    index_peter = None
    for i, house in enumerate(houses):
        if "mother" in house and house["mother"] == "Penny":
            index_penny = i
        if "name" in house and house["name"] == "Peter":
            index_peter = i
    if index_penny is not None and index_peter is not None:
        if not (index_penny < index_peter):
            return False

    # Clue 11: Arnold is somewhere to the right of the person whose birthday is in September.
    index_sept = None
    index_arnold = None
    for i, house in enumerate(houses):
        if "birthday" in house and house["birthday"] == "sept":
            index_sept = i
        if "name" in house and house["name"] == "Arnold":
            index_arnold = i
    if index_sept is not None and index_arnold is not None:
        if not (index_arnold > index_sept):
            return False

    # Clue 16: The person whose birthday is in September is somewhere to the left of the person whose mother's name is Kailyn.
    index_kailyn = None
    for i, house in enumerate(houses):
        if "mother" in house and house["mother"] == "Kailyn":
            index_kailyn = i
    if index_sept is not None and index_kailyn is not None:
        if not (index_sept < index_kailyn):
            return False

    return True

# Backtracking search.
def solve_houses(houses, avail_names, avail_mothers, avail_occs, avail_hairs, indices_to_fill, idx):
    if idx >= len(indices_to_fill):
        if check_constraints(houses):
            return houses
        return None

    house_index = indices_to_fill[idx]
    # Determine which keys are missing in this house. We only consider: "name", "mother", "occupation", "hair"
    keys_to_assign = []
    for key in ["name", "mother", "occupation", "hair"]:
        if key not in houses[house_index]:
            keys_to_assign.append(key)

    # For each missing key, get the corresponding available set.
    domains = {}
    for key in keys_to_assign:
        if key == "name":
            domains[key] = list(avail_names)
        elif key == "mother":
            domains[key] = list(avail_mothers)
        elif key == "occupation":
            domains[key] = list(avail_occs)
        elif key == "hair":
            domains[key] = list(avail_hairs)

    # If there is no missing key, just check constraints and move on.
    if not keys_to_assign:
        if check_constraints(houses):
            result = solve_houses(houses, avail_names, avail_mothers, avail_occs, avail_hairs, indices_to_fill, idx + 1)
            if result is not None:
                return result
        return None

    # Iterate over all combinations for the missing keys.
    for values in itertools.product(*(domains[key] for key in keys_to_assign)):
        # Create a copy of houses and assign the values for this house.
        houses_copy = copy.deepcopy(houses)
        assignment = dict(zip(keys_to_assign, values))
        houses_copy[house_index].update(assignment)
        if not check_constraints(houses_copy):
            continue

        # Update available sets
        new_avail_names = avail_names.copy()
        new_avail_mothers = avail_mothers.copy()
        new_avail_occs = avail_occs.copy()
        new_avail_hairs = avail_hairs.copy()

        if "name" in assignment:
            if assignment["name"] in new_avail_names:
                new_avail_names.remove(assignment["name"])
            else:
                continue
        if "mother" in assignment:
            if assignment["mother"] in new_avail_mothers:
                new_avail_mothers.remove(assignment["mother"])
            else:
                continue
        if "occupation" in assignment:
            if assignment["occupation"] in new_avail_occs:
                new_avail_occs.remove(assignment["occupation"])
            else:
                continue
        if "hair" in assignment:
            if assignment["hair"] in new_avail_hairs:
                new_avail_hairs.remove(assignment["hair"])
            else:
                continue

        result = solve_houses(houses_copy, new_avail_names, new_avail_mothers, new_avail_occs, new_avail_hairs, indices_to_fill, idx + 1)
        if result is not None:
            return result

    return None

def solve():
    houses = init_houses()
    # Determine the indices that still need assignments.
    # Houses 0, 1, 2, and 3 are missing some attributes.
    indices_to_fill = []
    for i in range(5):
        # We consider keys "name", "mother", "occupation", "hair"
        for key in ["name", "mother", "occupation", "hair"]:
            if key not in houses[i]:
                indices_to_fill.append(i)
                break

    # Set of available attributes after fixed assignments:
    used_names = set()
    for i in range(5):
        if "name" in houses[i]:
            used_names.add(houses[i]["name"])
    avail_names = set(names_full) - used_names

    used_mothers = set()
    for i in range(5):
        if "mother" in houses[i]:
            used_mothers.add(houses[i]["mother"])
    avail_mothers = set(mothers_full) - used_mothers

    used_occs = set()
    for i in range(5):
        if "occupation" in houses[i]:
            used_occs.add(houses[i]["occupation"])
    avail_occs = set(occupations_full) - used_occs

    used_hairs = set()
    for i in range(5):
        if "hair" in houses[i]:
            used_hairs.add(houses[i]["hair"])
    avail_hairs = set(hair_full) - used_hairs

    solution = solve_houses(houses, avail_names, avail_mothers, avail_occs, avail_hairs, indices_to_fill, 0)
    return solution

def main():
    solution = solve()
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"], "rows": []}}
    else:
        # Format the solution output according to the required structure.
        rows = []
        for i, house in enumerate(solution):
            row = [
                str(i + 1),
                house.get("name", ""),
                house.get("birthday", ""),
                house.get("mother", ""),
                house.get("occupation", ""),
                house.get("hair", "")
            ]
            rows.append(row)
        output = {"solution": {"header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"], "rows": rows}}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()