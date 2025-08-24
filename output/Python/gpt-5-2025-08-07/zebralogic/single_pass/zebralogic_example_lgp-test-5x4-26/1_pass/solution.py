import json

def solve():
    houses = [
        {"Name": None, "Height": None, "Mother": None, "HairColor": None} for _ in range(5)
    ]

    Names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    Heights = ["very short", "short", "tall", "average", "very tall"]
    Mothers = ["Janelle", "Kailyn", "Penny", "Holly", "Aniya"]
    HairColors = ["blonde", "black", "gray", "red", "brown"]

    forced_hair_by_name = {
        "Eric": "black",
        "Peter": "red",
        "Arnold": "brown",
    }

    def positions(mapping, key):
        # return index if key found in list mapping else None
        return mapping.get(key, None)

    def build_pos_maps(houses):
        pos_name = {}
        pos_height = {}
        pos_mother = {}
        pos_hair = {}
        for i, h in enumerate(houses):
            if h["Name"] is not None:
                pos_name[h["Name"]] = i
            if h["Height"] is not None:
                pos_height[h["Height"]] = i
            if h["Mother"] is not None:
                pos_mother[h["Mother"]] = i
            if h["HairColor"] is not None:
                pos_hair[h["HairColor"]] = i
        return pos_name, pos_height, pos_mother, pos_hair

    def check_constraints(houses):
        pos_name, pos_height, pos_mother, pos_hair = build_pos_maps(houses)

        # C8: Bob is in the fifth house (index 4)
        if "Bob" in pos_name and pos_name["Bob"] != 4:
            return False
        if houses[4]["Name"] is not None and houses[4]["Name"] != "Bob":
            return False

        # C14: Kailyn is in the third house (index 2)
        if houses[2]["Mother"] is not None and houses[2]["Mother"] != "Kailyn":
            return False
        if "Kailyn" in pos_mother and pos_mother["Kailyn"] != 2:
            return False

        # C4: The person who has black hair is not in the fourth house (index 3)
        if houses[3]["HairColor"] == "black":
            return False

        # C5: Eric is the person who has black hair (bi-conditional)
        if "Eric" in pos_name:
            idx = pos_name["Eric"]
            if houses[idx]["HairColor"] is not None and houses[idx]["HairColor"] != "black":
                return False
        if "black" in pos_hair:
            idx = pos_hair["black"]
            if houses[idx]["Name"] is not None and houses[idx]["Name"] != "Eric":
                return False

        # C9: The person who has red hair is Peter (bi-conditional)
        if "Peter" in pos_name:
            idx = pos_name["Peter"]
            if houses[idx]["HairColor"] is not None and houses[idx]["HairColor"] != "red":
                return False
        if "red" in pos_hair:
            idx = pos_hair["red"]
            if houses[idx]["Name"] is not None and houses[idx]["Name"] != "Peter":
                return False

        # C11: Arnold is the person who has brown hair (bi-conditional)
        if "Arnold" in pos_name:
            idx = pos_name["Arnold"]
            if houses[idx]["HairColor"] is not None and houses[idx]["HairColor"] != "brown":
                return False
        if "brown" in pos_hair:
            idx = pos_hair["brown"]
            if houses[idx]["Name"] is not None and houses[idx]["Name"] != "Arnold":
                return False

        # C1: tall <-> Holly
        if "tall" in pos_height:
            idx = pos_height["tall"]
            if houses[idx]["Mother"] is not None and houses[idx]["Mother"] != "Holly":
                return False
        if "Holly" in pos_mother:
            idx = pos_mother["Holly"]
            if houses[idx]["Height"] is not None and houses[idx]["Height"] != "tall":
                return False

        # C6: very short <-> Penny
        if "very short" in pos_height:
            idx = pos_height["very short"]
            if houses[idx]["Mother"] is not None and houses[idx]["Mother"] != "Penny":
                return False
        if "Penny" in pos_mother:
            idx = pos_mother["Penny"]
            if houses[idx]["Height"] is not None and houses[idx]["Height"] != "very short":
                return False

        # C2: Two houses between average and short (distance 3)
        if "average" in pos_height and "short" in pos_height:
            if abs(pos_height["average"] - pos_height["short"]) != 3:
                return False
        else:
            # partial check
            for label_a, label_b in [("average", "short"), ("short", "average")]:
                if label_a in pos_height and label_b not in pos_height:
                    p = pos_height[label_a]
                    candidates = []
                    if 0 <= p + 3 < 5:
                        candidates.append(p + 3)
                    if 0 <= p - 3 < 5:
                        candidates.append(p - 3)
                    if not candidates:
                        return False
                    # at least one candidate position must be still compatible (either unassigned or already assigned label_b)
                    ok = False
                    for q in candidates:
                        if houses[q]["Height"] is None or houses[q]["Height"] == label_b:
                            ok = True
                            break
                    if not ok:
                        return False

        # C3: gray hair is directly left of Janelle
        if "gray" in pos_hair:
            p = pos_hair["gray"]
            if p == 4:
                return False
            if houses[p + 1]["Mother"] is not None and houses[p + 1]["Mother"] != "Janelle":
                return False
        if "Janelle" in pos_mother:
            q = pos_mother["Janelle"]
            if q == 0:
                return False
            if houses[q - 1]["HairColor"] is not None and houses[q - 1]["HairColor"] != "gray":
                return False

        # C10: Kailyn directly left of short
        if "Kailyn" in pos_mother:
            p = pos_mother["Kailyn"]
            if p == 4:
                return False
            if houses[p + 1]["Height"] is not None and houses[p + 1]["Height"] != "short":
                return False
        if "short" in pos_height:
            q = pos_height["short"]
            if q == 0:
                return False
            if houses[q - 1]["Mother"] is not None and houses[q - 1]["Mother"] != "Kailyn":
                return False

        # C12: brown hair left of Janelle
        if "brown" in pos_hair and "Janelle" in pos_mother:
            if not (pos_hair["brown"] < pos_mother["Janelle"]):
                return False
        if "Janelle" in pos_mother and "brown" not in pos_hair:
            q = pos_mother["Janelle"]
            # There must be at least one position < q where brown could still be placed (hair unassigned or already brown)
            possible_left = any(
                (houses[i]["HairColor"] is None or houses[i]["HairColor"] == "brown") for i in range(q)
            )
            if not possible_left:
                return False
        if "brown" in pos_hair and "Janelle" not in pos_mother:
            p = pos_hair["brown"]
            # There must be at least one position > p for Janelle (mother unassigned or already Janelle)
            possible_right = any(
                (houses[i]["Mother"] is None or houses[i]["Mother"] == "Janelle") for i in range(p + 1, 5)
            )
            if not possible_right:
                return False

        # C7: Eric and gray hair are next to each other
        if "Eric" in pos_name:
            e = pos_name["Eric"]
            neighbors = []
            if e - 1 >= 0:
                neighbors.append(e - 1)
            if e + 1 < 5:
                neighbors.append(e + 1)
            # if both neighbors are assigned hair and none is gray => fail
            if neighbors:
                if all(houses[n]["HairColor"] is not None and houses[n]["HairColor"] != "gray" for n in neighbors):
                    return False
        if "gray" in pos_hair:
            g = pos_hair["gray"]
            neighbors = []
            if g - 1 >= 0:
                neighbors.append(g - 1)
            if g + 1 < 5:
                neighbors.append(g + 1)
            if neighbors:
                if all(houses[n]["Name"] is not None and houses[n]["Name"] != "Eric" for n in neighbors):
                    return False

        # C13: Aniya and very short are next to each other
        if "Aniya" in pos_mother:
            a = pos_mother["Aniya"]
            neighbors = []
            if a - 1 >= 0:
                neighbors.append(a - 1)
            if a + 1 < 5:
                neighbors.append(a + 1)
            if neighbors:
                if all(houses[n]["Height"] is not None and houses[n]["Height"] != "very short" for n in neighbors):
                    return False
        if "very short" in pos_height:
            vs = pos_height["very short"]
            neighbors = []
            if vs - 1 >= 0:
                neighbors.append(vs - 1)
            if vs + 1 < 5:
                neighbors.append(vs + 1)
            if neighbors:
                if all(houses[n]["Mother"] is not None and houses[n]["Mother"] != "Aniya" for n in neighbors):
                    return False

        # All-different constraints (no duplicates for assigned attributes)
        seen = set()
        for i in range(5):
            if houses[i]["Name"] is not None:
                if houses[i]["Name"] in seen:
                    return False
                seen.add(houses[i]["Name"])
        seen = set()
        for i in range(5):
            if houses[i]["Height"] is not None:
                if houses[i]["Height"] in seen:
                    return False
                seen.add(houses[i]["Height"])
        seen = set()
        for i in range(5):
            if houses[i]["Mother"] is not None:
                if houses[i]["Mother"] in seen:
                    return False
                seen.add(houses[i]["Mother"])
        seen = set()
        for i in range(5):
            if houses[i]["HairColor"] is not None:
                if houses[i]["HairColor"] in seen:
                    return False
                seen.add(houses[i]["HairColor"])

        return True

    def backtrack(idx, used_names, used_heights, used_mothers, used_hairs):
        if idx == 5:
            # Full assignment; final verify with constraints
            if check_constraints(houses):
                return True
            return False

        # Determine candidate sets
        # Names
        name_candidates = [n for n in Names if n not in used_names]
        # Apply C8: Bob must be in house 5 (index 4)
        if idx == 4:
            name_candidates = [n for n in name_candidates if n == "Bob"]
        else:
            name_candidates = [n for n in name_candidates if n != "Bob"]

        # Mothers
        mother_candidates = [m for m in Mothers if m not in used_mothers]
        # Apply C14: Kailyn in third house (index 2)
        if idx == 2:
            mother_candidates = [m for m in mother_candidates if m == "Kailyn"]
        else:
            mother_candidates = [m for m in mother_candidates if m != "Kailyn"]

        # Heights
        height_candidates_base = [h for h in Heights if h not in used_heights]

        # Try combinations
        for name in name_candidates:
            # Hair options depend on name
            if name in forced_hair_by_name:
                hair_opts = [forced_hair_by_name[name]]
            else:
                # Only Alice and Bob remain, cannot take black/red/brown
                hair_opts = [c for c in HairColors if c not in used_hairs and c in ("blonde", "gray")]
            # Ensure hair still available
            hair_opts = [c for c in hair_opts if c not in used_hairs]
            # House-specific restriction: black not allowed in index 3 (house 4)
            if idx == 3:
                hair_opts = [c for c in hair_opts if c != "black"]
            if not hair_opts:
                continue

            for mother in mother_candidates:
                # Now determine allowed heights considering equivalences:
                height_candidates = height_candidates_base[:]

                # C1: tall <-> Holly
                if mother == "Holly":
                    height_candidates = [h for h in height_candidates if h == "tall" or h not in Heights]  # keep tall if available
                else:
                    # if only tall remaining but mother != Holly, still could be assigned tall to another house; leave filtering to constraints
                    pass

                # C6: very short <-> Penny
                if mother == "Penny":
                    height_candidates = [h for h in height_candidates if h == "very short" or h not in Heights]

                # C10: Kailyn left of short is handled in constraints; mother here may be something else

                if not height_candidates:
                    continue

                for hair in hair_opts:
                    # Enforce bi-conditional hair to name immediately to reduce branching
                    if hair == "black" and name != "Eric":
                        continue
                    if hair == "red" and name != "Peter":
                        continue
                    if hair == "brown" and name != "Arnold":
                        continue
                    # Extra: prevent gray at last house if Janelle cannot be to its right; constraint check will catch but filter now if desired
                    # We'll rely on constraint check.

                    for height in height_candidates:
                        # Enforce tall<->Holly and very short<->Penny immediately
                        if height == "tall" and mother != "Holly":
                            continue
                        if height == "very short" and mother != "Penny":
                            continue
                        if height in used_heights or hair in used_hairs or mother in used_mothers or name in used_names:
                            continue

                        # Tentatively assign
                        houses[idx]["Name"] = name
                        houses[idx]["Mother"] = mother
                        houses[idx]["HairColor"] = hair
                        houses[idx]["Height"] = height

                        if check_constraints(houses):
                            used_names.add(name)
                            used_mothers.add(mother)
                            used_hairs.add(hair)
                            used_heights.add(height)

                            if backtrack(idx + 1, used_names, used_heights, used_mothers, used_hairs):
                                return True

                            used_names.remove(name)
                            used_mothers.remove(mother)
                            used_hairs.remove(hair)
                            used_heights.remove(height)

                        # Undo
                        houses[idx]["Name"] = None
                        houses[idx]["Mother"] = None
                        houses[idx]["HairColor"] = None
                        houses[idx]["Height"] = None

        return False

    solved = backtrack(0, set(), set(), set(), set())
    if not solved:
        raise RuntimeError("No solution found")

    # Prepare JSON output
    output = {
        "solution": {
            "header": ["House", "Name", "Height", "Mother", "HairColor"],
            "rows": []
        }
    }
    for i, h in enumerate(houses, start=1):
        row = [str(i), h["Name"], h["Height"], h["Mother"], h["HairColor"]]
        output["solution"]["rows"].append(row)

    print(json.dumps(output, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    solve()