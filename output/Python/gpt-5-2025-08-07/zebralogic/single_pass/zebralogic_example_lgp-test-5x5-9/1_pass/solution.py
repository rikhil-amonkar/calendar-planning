import json
from copy import deepcopy

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    categories = ["Name", "Drink", "Color", "Flower", "Hobby"]

    values = {
        "Name": ["Bob", "Arnold", "Peter", "Alice", "Eric"],
        "Drink": ["milk", "root beer", "coffee", "tea", "water"],
        "Color": ["blue", "green", "white", "yellow", "red"],
        "Flower": ["daffodils", "roses", "lilies", "tulips", "carnations"],
        "Hobby": ["painting", "cooking", "photography", "gardening", "knitting"],
    }

    # Initialize assignments: for each house, each category -> None
    assignments = {h: {cat: None for cat in categories} for h in houses}

    # Track used values per category
    used = {cat: set() for cat in categories}

    # Helper to find positions of assigned values for quick constraints checking
    def positions():
        pos = {cat: {} for cat in categories}
        for h in houses:
            for cat in categories:
                v = assignments[h][cat]
                if v is not None:
                    pos[cat][v] = h
        return pos

    # Consistency check based on all constraints
    def consistent():
        pos = positions()

        # 1. Alice is not in the fourth house.
        if "Alice" in pos["Name"] and pos["Name"]["Alice"] == 4:
            return False

        # 7. Eric is directly left of the tea drinker.
        pE = pos["Name"].get("Eric")
        pT = pos["Drink"].get("tea")
        if pE is not None and pE == 5:
            return False
        if pT is not None and pT == 1:
            return False
        if pE is not None and pT is not None and pE + 1 != pT:
            return False
        if pE is not None and pT is None:
            # tea must be at pE+1
            right = pE + 1
            if right < 1 or right > 5:
                return False
            if assignments[right]["Drink"] is not None and assignments[right]["Drink"] != "tea":
                return False
        if pT is not None and pE is None:
            left = pT - 1
            if left < 1 or left > 5:
                return False
            if assignments[left]["Name"] is not None and assignments[left]["Name"] != "Eric":
                return False

        # 13 and 8: Water is Peter; water is in third house; hence Peter in third house
        pW = pos["Drink"].get("water")
        pPeter = pos["Name"].get("Peter")
        if pW is not None and pW != 3:
            return False
        if pPeter is not None and pPeter != 3:
            return False
        if pW is not None and pPeter is not None and pW != pPeter:
            return False
        # If one known, enforce the other house alignment
        if pW is not None and assignments[pW]["Name"] is not None and assignments[pW]["Name"] != "Peter":
            return False
        if pPeter is not None and assignments[pPeter]["Drink"] is not None and assignments[pPeter]["Drink"] != "water":
            return False

        # 15 and 10: White is in second house and equals roses
        pWhite = pos["Color"].get("white")
        if pWhite is not None and pWhite != 2:
            return False
        # If house 2 color assigned but not white, contradiction
        if assignments[2]["Color"] is not None and assignments[2]["Color"] != "white":
            return False
        # White equals roses
        pRoses = pos["Flower"].get("roses")
        if pWhite is not None and pRoses is not None and pWhite != pRoses:
            return False
        # If in any house color is white but flower is not roses or vice versa
        for h in houses:
            c = assignments[h]["Color"]
            f = assignments[h]["Flower"]
            if c == "white" and f is not None and f != "roses":
                return False
            if f == "roses" and c is not None and c != "white":
                return False

        # 3 and 4: Green = coffee = lilies
        pGreen = pos["Color"].get("green")
        pCoffee = pos["Drink"].get("coffee")
        pLilies = pos["Flower"].get("lilies")
        # Equalities among any assigned of these three
        if pGreen is not None and pCoffee is not None and pGreen != pCoffee:
            return False
        if pGreen is not None and pLilies is not None and pGreen != pLilies:
            return False
        if pCoffee is not None and pLilies is not None and pCoffee != pLilies:
            return False
        # Within-house consistency if any of the trio is set
        for h in houses:
            c = assignments[h]["Color"]
            d = assignments[h]["Drink"]
            f = assignments[h]["Flower"]
            if c == "green":
                if (d is not None and d != "coffee") or (f is not None and f != "lilies"):
                    return False
            if d == "coffee":
                if (c is not None and c != "green") or (f is not None and f != "lilies"):
                    return False
            if f == "lilies":
                if (c is not None and c != "green") or (d is not None and d != "coffee"):
                    return False

        # 2 and 14: root beer = gardening = carnations
        pRoot = pos["Drink"].get("root beer")
        pGarden = pos["Hobby"].get("gardening")
        pCarn = pos["Flower"].get("carnations")
        if pRoot is not None and pGarden is not None and pRoot != pGarden:
            return False
        if pRoot is not None and pCarn is not None and pRoot != pCarn:
            return False
        if pGarden is not None and pCarn is not None and pGarden != pCarn:
            return False
        for h in houses:
            d = assignments[h]["Drink"]
            hb = assignments[h]["Hobby"]
            fl = assignments[h]["Flower"]
            if d == "root beer":
                if (hb is not None and hb != "gardening") or (fl is not None and fl != "carnations"):
                    return False
            if hb == "gardening":
                # must also be root beer and carnations at same house if assigned
                if (d is not None and d != "root beer") or (fl is not None and fl != "carnations"):
                    return False
                # Also if root beer assigned elsewhere, contradiction
                if pRoot is not None and pRoot != h:
                    return False
                if pCarn is not None and pCarn != h:
                    return False
            if fl == "carnations":
                if (d is not None and d != "root beer") or (hb is not None and hb != "gardening"):
                    return False
                if pRoot is not None and pRoot != h:
                    return False
                if pGarden is not None and pGarden != h:
                    return False

        # 6: cooking = blue
        pCooking = pos["Hobby"].get("cooking")
        pBlue = pos["Color"].get("blue")
        if pCooking is not None and pBlue is not None and pCooking != pBlue:
            return False
        for h in houses:
            hb = assignments[h]["Hobby"]
            c = assignments[h]["Color"]
            if hb == "cooking" and c is not None and c != "blue":
                return False
            if c == "blue" and hb is not None and hb != "cooking":
                return False

        # 9: Arnold = photography
        pArnold = pos["Name"].get("Arnold")
        pPhoto = pos["Hobby"].get("photography")
        if pArnold is not None and pPhoto is not None and pArnold != pPhoto:
            return False
        for h in houses:
            nm = assignments[h]["Name"]
            hb = assignments[h]["Hobby"]
            if nm == "Arnold" and hb is not None and hb != "photography":
                return False
            if hb == "photography" and nm is not None and nm != "Arnold":
                return False

        # 5: Blue is somewhere to the right of the daffodils.
        pDaf = pos["Flower"].get("daffodils")
        if pBlue is not None and pDaf is not None and not (pBlue > pDaf):
            return False
        if pBlue is not None and pDaf is None:
            if pBlue == 1:
                return False
            # ensure at least one house to the left can still be 'daffodils'
            possible = False
            for k in range(1, pBlue):
                if assignments[k]["Flower"] is None:
                    possible = True
                    break
                if assignments[k]["Flower"] == "daffodils":
                    possible = True
                    break
            # Also if 'daffodils' already used elsewhere, pos would be known; handled above.
            if not possible:
                return False
        if pDaf is not None and pBlue is None:
            if pDaf == 5:
                return False
            possible = False
            for k in range(pDaf + 1, 6):
                if assignments[k]["Color"] is None:
                    possible = True
                    break
                if assignments[k]["Color"] == "blue":
                    possible = True
                    break
            if not possible:
                return False

        # 12: cooking is left of painting
        pPaint = pos["Hobby"].get("painting")
        if pCooking is not None and pPaint is not None and not (pCooking < pPaint):
            return False
        if pCooking is not None and pPaint is None:
            if pCooking == 5:
                return False
            possible = False
            for k in range(pCooking + 1, 6):
                if assignments[k]["Hobby"] is None or assignments[k]["Hobby"] == "painting":
                    possible = True
                    break
            if not possible:
                return False
        if pPaint is not None and pCooking is None:
            if pPaint == 1:
                return False
            possible = False
            for k in range(1, pPaint):
                if assignments[k]["Hobby"] is None or assignments[k]["Hobby"] == "cooking":
                    possible = True
                    break
            if not possible:
                return False

        # 11: one house between carnations and red (distance 2)
        pRed = pos["Color"].get("red")
        if pCarn is not None and pRed is not None and abs(pCarn - pRed) != 2:
            return False
        if pCarn is not None and pRed is None:
            candidates = []
            if pCarn - 2 >= 1:
                candidates.append(pCarn - 2)
            if pCarn + 2 <= 5:
                candidates.append(pCarn + 2)
            if not candidates:
                return False
            ok = False
            for r in candidates:
                if assignments[r]["Color"] is None or assignments[r]["Color"] == "red":
                    ok = True
                    break
            if not ok:
                return False
        if pRed is not None and pCarn is None:
            candidates = []
            if pRed - 2 >= 1:
                candidates.append(pRed - 2)
            if pRed + 2 <= 5:
                candidates.append(pRed + 2)
            if not candidates:
                return False
            ok = False
            for r in candidates:
                if assignments[r]["Flower"] is None or assignments[r]["Flower"] == "carnations":
                    ok = True
                    break
            if not ok:
                return False

        return True

    # Assign a value to a variable
    def set_value(h, cat, val):
        # uniqueness per category
        if val in used[cat]:
            return False
        current = assignments[h][cat]
        if current is not None and current != val:
            return False
        # Direct contradictions based on some simple constraints
        if cat == "Name":
            if val == "Alice" and h == 4:
                return False
            if val == "Eric" and h == 5:
                return False
            if val == "Peter" and h != 3:
                return False
        if cat == "Drink":
            if val == "tea" and h == 1:
                return False
            if val == "water" and h != 3:
                return False
        if cat == "Color":
            if val == "white" and h != 2:
                return False
        # Tentatively assign
        assignments[h][cat] = val
        used[cat].add(val)
        if not consistent():
            # undo
            used[cat].remove(val)
            assignments[h][cat] = current
            return False
        return True

    def unset_value(h, cat, val):
        assignments[h][cat] = None
        used[cat].remove(val)

    # Select next variable using MRV heuristic
    def select_unassigned():
        best = None
        best_domain = None
        for h in houses:
            for cat in categories:
                if assignments[h][cat] is None:
                    # compute domain
                    domain = [v for v in values[cat] if v not in used[cat]]
                    # quick basic prunes
                    if cat == "Name":
                        if h == 4 and "Alice" in domain:
                            domain.remove("Alice")
                        if h == 5 and "Eric" in domain:
                            domain.remove("Eric")
                        if h != 3 and "Peter" in domain:
                            # Peter fixed at 3
                            domain.remove("Peter")
                    if cat == "Drink":
                        if h == 1 and "tea" in domain:
                            domain.remove("tea")
                        if h != 3 and "water" in domain:
                            domain.remove("water")
                    if cat == "Color":
                        if h != 2 and "white" in domain:
                            domain.remove("white")
                        if h == 2:
                            domain = ["white"] if "white" not in used["Color"] else []
                    # If this domain is empty, early return to force backtrack
                    if best_domain is None or len(domain) < len(best_domain):
                        best = (h, cat)
                        best_domain = domain
                        if len(best_domain) == 0:
                            return best, best_domain
        return best, best_domain

    def backtrack():
        # Check if complete
        done = True
        for h in houses:
            for cat in categories:
                if assignments[h][cat] is None:
                    done = False
                    break
            if not done:
                break
        if done:
            return True

        (h, cat), domain = select_unassigned()
        if domain is None:
            return False
        for val in domain:
            if set_value(h, cat, val):
                if backtrack():
                    return True
                unset_value(h, cat, val)
        return False

    # Initial forced assignments from constraints:
    # 13 & 8: House 3 drink water, and Peter is the water drinker
    set_value(3, "Drink", "water")
    set_value(3, "Name", "Peter")
    # 15 & 10: House 2 color white and roses
    set_value(2, "Color", "white")
    set_value(2, "Flower", "roses")

    # Solve
    if not backtrack():
        raise ValueError("No solution found")

    # Build output
    header = ["House", "Name", "Drink", "Color", "Flower", "Hobby"]
    rows = []
    for h in houses:
        row = [str(h), assignments[h]["Name"], assignments[h]["Drink"], assignments[h]["Color"], assignments[h]["Flower"], assignments[h]["Hobby"]]
        rows.append(row)

    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))