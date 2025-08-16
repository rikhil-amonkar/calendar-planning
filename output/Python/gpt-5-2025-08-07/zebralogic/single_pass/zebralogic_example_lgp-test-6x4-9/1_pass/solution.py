import json

# Zebra puzzle solver for the given 6-house puzzle

houses = [1, 2, 3, 4, 5, 6]

Names = ["Carol", "Bob", "Alice", "Arnold", "Eric", "Peter"]
PhoneModels = ["samsung galaxy s21", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9", "xiaomi mi 11"]
Nationalities = ["swede", "chinese", "norwegian", "dane", "german", "brit"]
Colors = ["blue", "red", "yellow", "green", "white", "purple"]

# Assignments per house (index 0..5 corresponds to house 1..6)
assign = {
    "Name": [None] * 6,
    "PhoneModel": [None] * 6,
    "Nationality": [None] * 6,
    "Color": [None] * 6
}

# Used sets per category
used = {
    "Name": set(),
    "PhoneModel": set(),
    "Nationality": set(),
    "Color": set()
}

categories = ["Name", "PhoneModel", "Nationality", "Color"]
values_by_cat = {
    "Name": Names,
    "PhoneModel": PhoneModels,
    "Nationality": Nationalities,
    "Color": Colors
}

def pos_of(category, value):
    arr = assign[category]
    for i, v in enumerate(arr):
        if v == value:
            return i + 1  # houses are 1-based
    return None

def check_equivalence(cat1, val1, cat2, val2):
    # For all houses, check the bi-implication between cat1=val1 and cat2=val2
    for i in range(6):
        v1 = assign[cat1][i]
        v2 = assign[cat2][i]
        if v1 == val1:
            if v2 is not None and v2 != val2:
                return False
        if v2 == val2:
            if v1 is not None and v1 != val1:
                return False
    return True

def check_directional_pair(cat1, val1, cat2, val2, offset):
    # Check that position(cat2=val2) == position(cat1=val1) + offset
    p1 = pos_of(cat1, val1)
    p2 = pos_of(cat2, val2)
    if p1 is not None and p2 is not None:
        return p2 == p1 + offset
    if p1 is not None and p2 is None:
        target = p1 + offset
        if target < 1 or target > 6:
            return False
        # The target house must be compatible with cat2=val2
        v = assign[cat2][target - 1]
        if v is not None and v != val2:
            return False
    if p1 is None and p2 is not None:
        # Then p1 must be p2 - offset
        target = p2 - offset
        if target < 1 or target > 6:
            return False
        v = assign[cat1][target - 1]
        if v is not None and v != val1:
            return False
    return True

def at_house(category, house_index, value):
    v = assign[category][house_index - 1]
    if v is not None and v != value:
        return False
    pos = pos_of(category, value)
    if pos is not None and pos != house_index:
        return False
    return True

def exists_right_position_for(color_left, color_right):
    # Helper for red-left-of-white viability check
    pr = pos_of("Color", color_left)
    pw = pos_of("Color", color_right)
    if pr is not None and pw is None:
        # ensure there exists some position to the right that can still be white
        for i in range(pr, 6):
            c = assign["Color"][i]
            if c is None or c == color_right:
                return True
        return False
    if pw is not None and pr is None:
        # ensure there exists a position to the left that can still be red
        for i in range(0, pw - 1):
            c = assign["Color"][i]
            if c is None or c == color_left:
                return True
        return False
    return True

def exists_left_position_for_leftof(val_left_cat, cat_left, val_right_cat, cat_right):
    # Generic viability: ensure left position exists
    pl = pos_of(cat_left, val_left_cat)
    pr = pos_of(cat_right, val_right_cat)
    if pl is not None and pr is None:
        target = pl + 1
        if target < 1 or target > 6:
            return False
        v = assign[cat_right][target - 1]
        if v is not None and v != val_right_cat:
            return False
    if pr is not None and pl is None:
        target = pr - 1
        if target < 1 or target > 6:
            return False
        v = assign[cat_left][target - 1]
        if v is not None and v != val_left_cat:
            return False
    return True

def exists_between_constraint(nat1, nat2):
    # There is exactly one house between nat1 and nat2
    p1 = pos_of("Nationality", nat1)
    p2 = pos_of("Nationality", nat2)
    if p1 is not None and p2 is not None:
        return abs(p1 - p2) == 2
    # Partial viability checks
    if p1 is not None and p2 is None:
        candidates = []
        for d in [-2, 2]:
            target = p1 + d
            if 1 <= target <= 6:
                v = assign["Nationality"][target - 1]
                if v is None or v == nat2:
                    candidates.append(target)
        return len(candidates) > 0
    if p2 is not None and p1 is None:
        candidates = []
        for d in [-2, 2]:
            target = p2 + d
            if 1 <= target <= 6:
                v = assign["Nationality"][target - 1]
                if v is None or v == nat1:
                    candidates.append(target)
        return len(candidates) > 0
    return True

def exists_to_right_constraint(phone_left, name_right):
    # phone_left's house is somewhere to the left of name_right's house
    pl = pos_of("PhoneModel", phone_left)
    pr = pos_of("Name", name_right)
    if pl is not None and pr is not None:
        return pl < pr
    if pl is not None and pr is None:
        # ensure there exists some house to the right for name
        for i in range(pl, 6):
            v = assign["Name"][i]
            if v is None or v == name_right:
                return True
        return False
    if pr is not None and pl is None:
        # ensure there exists some house to the left for phone
        for i in range(0, pr - 1):
            v = assign["PhoneModel"][i]
            if v is None or v == phone_left:
                return True
        return False
    return True

def constraints_ok():
    # C1: Carol is not in the third house.
    if assign["Name"][2] == "Carol":
        return False

    # C2: There is one house between the Dane and the British person.
    if not exists_between_constraint("dane", "brit"):
        return False

    # C3: Carol is the person whose favorite color is green. (Equivalence)
    if not check_equivalence("Name", "Carol", "Color", "green"):
        return False

    # C4: Arnold is directly left of Alice.
    if not check_directional_pair("Name", "Arnold", "Name", "Alice", 1):
        return False

    # C5: Alice is the German. (Equivalence)
    if not check_equivalence("Name", "Alice", "Nationality", "german"):
        return False

    # C6: OnePlus 9 <-> purple
    if not check_equivalence("PhoneModel", "oneplus 9", "Color", "purple"):
        return False

    # C7: Huawei P50 is not in the third house.
    v = assign["PhoneModel"][2]
    if v is not None and v == "huawei p50":
        return False

    # C8: Samsung Galaxy S21 is in the fifth house.
    # - House 5 phone must be s21 if assigned
    v5 = assign["PhoneModel"][4]
    if v5 is not None and v5 != "samsung galaxy s21":
        return False
    # - If s21 assigned, must be at house 5
    ps21 = pos_of("PhoneModel", "samsung galaxy s21")
    if ps21 is not None and ps21 != 5:
        return False

    # C9: white is somewhere to the right of red.
    pred = pos_of("Color", "red")
    pwhite = pos_of("Color", "white")
    if pred is not None and pwhite is not None and not (pred < pwhite):
        return False
    if not exists_right_position_for("red", "white"):
        return False

    # C10: s21 <-> Bob
    if not check_equivalence("PhoneModel", "samsung galaxy s21", "Name", "Bob"):
        return False

    # C11: Dane <-> yellow
    if not check_equivalence("Nationality", "dane", "Color", "yellow"):
        return False

    # C12: s21 is somewhere to the left of Peter.
    if not exists_to_right_constraint("samsung galaxy s21", "Peter"):
        return False

    # C13: blue <-> Peter
    if not check_equivalence("Color", "blue", "Name", "Peter"):
        return False

    # C14: Peter <-> British
    if not check_equivalence("Name", "Peter", "Nationality", "brit"):
        return False

    # C15: s21 directly left of iphone 13
    if not check_directional_pair("PhoneModel", "samsung galaxy s21", "PhoneModel", "iphone 13", 1):
        return False

    # C16: Norwegian <-> purple (combined with C6 implies Norwegian uses oneplus 9)
    if not check_equivalence("Nationality", "norwegian", "Color", "purple"):
        return False

    # C17: Xiaomi Mi 11 <-> Chinese
    if not check_equivalence("PhoneModel", "xiaomi mi 11", "Nationality", "chinese"):
        return False

    return True

def possible_values(category, house_idx):
    # Determine possible values for a given variable considering used values and unary constraints
    vals = [v for v in values_by_cat[category] if v not in used[category]]

    # Unary constraints
    if category == "Name":
        # C1: Carol not in third house
        if house_idx == 2 and "Carol" in vals:
            vals.remove("Carol")
        # Cross with other assigned values in same house
        ph = assign["PhoneModel"][house_idx]
        nat = assign["Nationality"][house_idx]
        col = assign["Color"][house_idx]
        if ph == "samsung galaxy s21":
            vals = [v for v in vals if v == "Bob"]
        if nat == "brit":
            vals = [v for v in vals if v == "Peter"]
        if nat == "german":
            vals = [v for v in vals if v == "Alice"]
        if col == "blue":
            vals = [v for v in vals if v == "Peter"]
        if col == "green":
            vals = [v for v in vals if v == "Carol"]
    elif category == "PhoneModel":
        # C7: Huawei not in 3rd
        if house_idx == 2 and "huawei p50" in vals:
            vals.remove("huawei p50")
        # C8: s21 in 5th
        if house_idx == 4:
            vals = [v for v in vals if v == "samsung galaxy s21"]
        # Cross with same-house attributes
        nm = assign["Name"][house_idx]
        nat = assign["Nationality"][house_idx]
        col = assign["Color"][house_idx]
        if nm == "Bob":
            vals = [v for v in vals if v == "samsung galaxy s21"]
        if nat == "chinese":
            vals = [v for v in vals if v == "xiaomi mi 11"]
        if col == "purple":
            vals = [v for v in vals if v == "oneplus 9"]
    elif category == "Nationality":
        nm = assign["Name"][house_idx]
        col = assign["Color"][house_idx]
        ph = assign["PhoneModel"][house_idx]
        if nm == "Peter":
            vals = [v for v in vals if v == "brit"]
        if nm == "Alice":
            vals = [v for v in vals if v == "german"]
        if col == "yellow":
            vals = [v for v in vals if v == "dane"]
        if col == "purple":
            vals = [v for v in vals if v == "norwegian"]
        if ph == "xiaomi mi 11":
            vals = [v for v in vals if v == "chinese"]
    elif category == "Color":
        nm = assign["Name"][house_idx]
        nat = assign["Nationality"][house_idx]
        ph = assign["PhoneModel"][house_idx]
        if nm == "Peter":
            vals = [v for v in vals if v == "blue"]
        if nm == "Carol":
            vals = [v for v in vals if v == "green"]
        if nat == "dane":
            vals = [v for v in vals if v == "yellow"]
        if nat == "norwegian":
            vals = [v for v in vals if v == "purple"]
        if ph == "oneplus 9":
            vals = [v for v in vals if v == "purple"]
    return vals

def select_unassigned_variable():
    best = None
    best_domain = None
    best_len = 999
    for cat in categories:
        for i in range(6):
            if assign[cat][i] is None:
                domain = possible_values(cat, i)
                l = len(domain)
                if l < best_len:
                    best_len = l
                    best = (cat, i)
                    best_domain = domain
                if l == 0:
                    return (cat, i), []
    return best, best_domain

def assign_value(category, idx, value):
    assign[category][idx] = value
    used[category].add(value)

def unassign_value(category, idx, value):
    assign[category][idx] = None
    used[category].remove(value)

def backtrack():
    var, domain = select_unassigned_variable()
    if var is None:
        # All assigned
        return True
    cat, idx = var
    for val in domain:
        assign_value(cat, idx, val)
        if constraints_ok():
            if backtrack():
                return True
        unassign_value(cat, idx, val)
    return False

# Solve
solved = backtrack()

# Prepare JSON output
output = {
    "solution": {
        "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
        "rows": []
    }
}

if solved:
    for i in range(6):
        row = [
            str(i + 1),
            assign["Name"][i],
            assign["PhoneModel"][i],
            assign["Nationality"][i],
            assign["Color"][i]
        ]
        output["solution"]["rows"].append(row)
else:
    # In unexpected case of no solution, still output structure with Nones
    for i in range(6):
        row = [
            str(i + 1),
            assign["Name"][i],
            assign["PhoneModel"][i],
            assign["Nationality"][i],
            assign["Color"][i]
        ]
        output["solution"]["rows"].append(row)

print(json.dumps(output, ensure_ascii=False))