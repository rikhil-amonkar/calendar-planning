import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]

    Names = ["Carol", "Bob", "Alice", "Arnold", "Eric", "Peter"]
    Phones = ["samsung galaxy s21", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9", "xiaomi mi 11"]
    Nationalities = ["swede", "chinese", "norwegian", "dane", "german", "brit"]
    Colors = ["blue", "red", "yellow", "green", "white", "purple"]

    # Allowed sets per house based on structural constraints
    allowed_names_by_house = {
        1: {"Carol", "Arnold", "Eric"},
        2: {"Carol", "Arnold", "Alice", "Eric"},
        3: {"Alice", "Eric"},
        4: {"Carol", "Eric"},
        5: {"Bob"},
        6: {"Peter"},
    }
    allowed_phones_by_house = {
        1: {"oneplus 9", "xiaomi mi 11", "huawei p50", "google pixel 6"},
        2: {"oneplus 9", "xiaomi mi 11", "huawei p50", "google pixel 6"},
        3: {"oneplus 9", "xiaomi mi 11", "google pixel 6"},  # not huawei at house 3
        4: {"oneplus 9", "xiaomi mi 11", "huawei p50", "google pixel 6"},
        5: {"samsung galaxy s21"},
        6: {"iphone 13"},
    }
    allowed_nationalities_by_house = {
        1: set(Nationalities),
        2: set(Nationalities),
        3: set(Nationalities),
        4: {"dane"},   # From clue 2 and 14: Brit at 6, Dane must be 4 (one house between)
        5: set(Nationalities),
        6: {"brit"},   # From clues 12, 10, 15, 13, 14 -> Peter at 6 and is Brit
    }
    allowed_colors_by_house = {
        1: {"red", "green", "purple"},
        2: {"red", "green", "purple"},
        3: {"red", "purple"},  # Carol is green and not in house 3
        4: {"yellow"},
        5: {"white"},
        6: {"blue"},
    }

    # Initialize assignment structure
    assignments = {
        h: {"Name": None, "PhoneModel": None, "Nationality": None, "Color": None}
        for h in houses
    }

    # Used sets to ensure uniqueness
    used = {
        "Name": set(),
        "PhoneModel": set(),
        "Nationality": set(),
        "Color": set(),
    }

    # Helper functions enforcing equivalence constraints
    def enforce_name_nationality_color_phone(name, nat, color, phone, house):
        # Return (name, nat, color, phone) possibly adjusted or None if impossible
        # Name-based constraints
        if name == "Bob":
            if house != 5:
                return None
            if phone is not None and phone != "samsung galaxy s21":
                return None
            phone = "samsung galaxy s21"
        if name == "Peter":
            if house != 6:
                return None
            if color is not None and color != "blue":
                return None
            color = "blue"
            if nat is not None and nat != "brit":
                return None
            nat = "brit"
            if phone is not None and phone != "iphone 13":
                return None
            phone = "iphone 13"
        if name == "Alice":
            if nat is not None and nat != "german":
                return None
            nat = "german"
        if name == "Carol":
            if color is not None and color != "green":
                return None
            color = "green"

        # Nationality-based constraints
        if nat == "german":
            if name is not None and name != "Alice":
                return None
            name = "Alice"
        if nat == "norwegian":
            if color is not None and color != "purple":
                return None
            color = "purple"
            if phone is not None and phone != "oneplus 9":
                return None
            phone = "oneplus 9"
        if nat == "brit":
            if name is not None and name != "Peter":
                return None
            name = "Peter"
            if color is not None and color != "blue":
                return None
            color = "blue"
        if nat == "dane":
            if color is not None and color != "yellow":
                return None
            color = "yellow"
        if nat == "chinese":
            if phone is not None and phone != "xiaomi mi 11":
                return None
            phone = "xiaomi mi 11"

        # Phone-based constraints
        if phone == "samsung galaxy s21":
            if house != 5:
                return None
            if name is not None and name != "Bob":
                return None
            name = "Bob"
        if phone == "iphone 13":
            if house != 6:
                return None
            if name is not None and name != "Peter":
                return None
            name = "Peter"
        if phone == "oneplus 9":
            if color is not None and color != "purple":
                return None
            color = "purple"
            if nat is not None and nat != "norwegian":
                return None
            nat = "norwegian"
        if phone == "xiaomi mi 11":
            if nat is not None and nat != "chinese":
                return None
            nat = "chinese"

        # Color-based constraints
        if color == "green":
            if name is not None and name != "Carol":
                return None
            name = "Carol"
        if color == "purple":
            if phone is not None and phone != "oneplus 9":
                return None
            phone = "oneplus 9"
            if nat is not None and nat != "norwegian":
                return None
            nat = "norwegian"
        if color == "blue":
            if name is not None and name != "Peter":
                return None
            name = "Peter"
        if color == "yellow":
            if nat is not None and nat != "dane":
                return None
            nat = "dane"

        return name, nat, color, phone

    # Partial validation for adjacency and structural constraints
    def validate_partial(assignments):
        # Arnold directly left of Alice
        pos = {h: assignments[h]["Name"] for h in houses}
        pos_by_name = {v: k for k, v in pos.items() if v is not None}
        if "Arnold" in pos_by_name and "Alice" in pos_by_name:
            if pos_by_name["Arnold"] + 1 != pos_by_name["Alice"]:
                return False
        else:
            # If one is assigned, ensure feasibility remains
            if "Arnold" in pos_by_name and "Alice" not in pos_by_name:
                a = pos_by_name["Arnold"]
                if a + 1 not in houses:
                    return False
                # The next house must be available for Alice
                if assignments[a + 1]["Name"] is not None and assignments[a + 1]["Name"] != "Alice":
                    return False
                if "Alice" not in allowed_names_by_house[a + 1]:
                    return False
            if "Alice" in pos_by_name and "Arnold" not in pos_by_name:
                b = pos_by_name["Alice"]
                if b - 1 not in houses:
                    return False
                if assignments[b - 1]["Name"] is not None and assignments[b - 1]["Name"] != "Arnold":
                    return False
                if "Arnold" not in allowed_names_by_house[b - 1]:
                    return False

        # House-specific constraints already in allowed maps:
        # - Carol not in 3 ensured by allowed_names_by_house
        # - Huawei not in 3 ensured by allowed_phones_by_house

        # Samsung galaxy s21 is in the 5th house and directly left of iPhone 13
        # Enforced via allowed_phones_by_house and equivalences

        # White to right of Red: partial feasibility check
        # Since white is fixed at 5, disallow red at house >=6
        for h in houses:
            if assignments[h]["Color"] == "red" and h >= 6:
                return False

        # Dane at 4 and Brit at 6 (from deductions, but ensure consistency if both assigned)
        # If both nationalities assigned, ensure exactly one house between
        nat_by_house = {h: assignments[h]["Nationality"] for h in houses}
        pos_dane = None
        pos_brit = None
        for h in houses:
            if nat_by_house[h] == "dane":
                pos_dane = h
            if nat_by_house[h] == "brit":
                pos_brit = h
        if pos_dane is not None and pos_brit is not None:
            if abs(pos_dane - pos_brit) != 2:
                return False

        return True

    # Final validation to ensure all clues satisfied
    def validate_final(assignments):
        # Uniqueness
        for attr in ["Name", "PhoneModel", "Nationality", "Color"]:
            values = [assignments[h][attr] for h in houses]
            if len(set(values)) != 6:
                return False

        # Build reverse lookup
        name_pos = {assignments[h]["Name"]: h for h in houses}
        phone_pos = {assignments[h]["PhoneModel"]: h for h in houses}
        nat_pos = {assignments[h]["Nationality"]: h for h in houses}
        color_pos = {assignments[h]["Color"]: h for h in houses}

        # 1. Carol not in third
        if name_pos["Carol"] == 3:
            return False
        # 2. One house between Dane and British
        if abs(nat_pos["dane"] - nat_pos["brit"]) != 2:
            return False
        # 3. Carol is green
        if assignments[name_pos["Carol"]]["Color"] != "green":
            return False
        # 4. Arnold directly left of Alice
        if name_pos["Arnold"] + 1 != name_pos["Alice"]:
            return False
        # 5. Alice is German
        if assignments[name_pos["Alice"]]["Nationality"] != "german":
            return False
        # 6. OnePlus 9 user loves purple
        if assignments[phone_pos["oneplus 9"]]["Color"] != "purple":
            return False
        # 7. Huawei not in third
        if phone_pos.get("huawei p50", None) == 3:
            return False
        # 8. SGS21 in fifth
        if phone_pos["samsung galaxy s21"] != 5:
            return False
        # 9. White to the right of red
        if color_pos["white"] <= color_pos["red"]:
            return False
        # 10. SGS21 is Bob
        if assignments[phone_pos["samsung galaxy s21"]]["Name"] != "Bob":
            return False
        # 11. Dane loves yellow
        if assignments[nat_pos["dane"]]["Color"] != "yellow":
            return False
        # 12. SGS21 to the left of Peter
        if phone_pos["samsung galaxy s21"] >= name_pos["Peter"]:
            return False
        # 13. Blue is Peter
        if assignments[color_pos["blue"]]["Name"] != "Peter":
            return False
        # 14. Peter is British
        if assignments[name_pos["Peter"]]["Nationality"] != "brit":
            return False
        # 15. SGS21 directly left of iPhone 13
        if phone_pos["samsung galaxy s21"] + 1 != phone_pos["iphone 13"]:
            return False
        # 16. Norwegian is purple
        if assignments[nat_pos["norwegian"]]["Color"] != "purple":
            return False
        # 17. Xiaomi Mi 11 is the Chinese
        if assignments[phone_pos["xiaomi mi 11"]]["Nationality"] != "chinese":
            return False

        return True

    order = [1, 2, 3, 4, 5, 6]

    solution = None

    def backtrack(idx):
        nonlocal solution
        if idx == len(order):
            if validate_final(assignments):
                solution = {h: assignments[h].copy() for h in houses}
                return True
            return False

        h = order[idx]

        # Determine candidate names for this house
        for name in sorted(n for n in allowed_names_by_house[h] if n not in used["Name"]):
            # Determine candidate nationalities
            for nat in sorted(nc for nc in allowed_nationalities_by_house[h] if nc not in used["Nationality"]):
                # Preliminary equivalence checks for name/nationality consistency
                # e.g., if name = Carol and nat = brit (would force Peter) - handled in enforce fn
                # Determine candidate phones and colors via allowed sets
                for phone in sorted(p for p in allowed_phones_by_house[h] if p not in used["PhoneModel"]):
                    for color in sorted(c for c in allowed_colors_by_house[h] if c not in used["Color"]):
                        # Apply equivalence and constraint enforcement
                        enforced = enforce_name_nationality_color_phone(name, nat, color, phone, h)
                        if enforced is None:
                            continue
                        en_name, en_nat, en_color, en_phone = enforced

                        # Re-check within allowed sets after enforcement
                        if en_name not in allowed_names_by_house[h]:
                            continue
                        if en_phone not in allowed_phones_by_house[h]:
                            continue
                        if en_nat not in allowed_nationalities_by_house[h] and assignments[h]["Nationality"] != en_nat:
                            # If the house had a fixed nationality different (only possible for house 4,6)
                            continue
                        if en_color not in allowed_colors_by_house[h]:
                            continue

                        # Ensure not already used
                        if en_name in used["Name"] or en_phone in used["PhoneModel"] or en_nat in used["Nationality"] or en_color in used["Color"]:
                            continue

                        # Assign
                        prev = assignments[h].copy()
                        assignments[h]["Name"] = en_name
                        assignments[h]["PhoneModel"] = en_phone
                        assignments[h]["Nationality"] = en_nat
                        assignments[h]["Color"] = en_color

                        used["Name"].add(en_name)
                        used["PhoneModel"].add(en_phone)
                        used["Nationality"].add(en_nat)
                        used["Color"].add(en_color)

                        # Partial validation
                        if validate_partial(assignments):
                            if backtrack(idx + 1):
                                return True

                        # Undo
                        used["Name"].remove(en_name)
                        used["PhoneModel"].remove(en_phone)
                        used["Nationality"].remove(en_nat)
                        used["Color"].remove(en_color)
                        assignments[h] = prev

        return False

    backtrack(0)

    if not solution:
        raise RuntimeError("No solution found")

    # Build output rows
    rows = []
    header = ["House", "Name", "PhoneModel", "Nationality", "Color"]
    for h in houses:
        row = [str(h), solution[h]["Name"], solution[h]["PhoneModel"], solution[h]["Nationality"], solution[h]["Color"]]
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