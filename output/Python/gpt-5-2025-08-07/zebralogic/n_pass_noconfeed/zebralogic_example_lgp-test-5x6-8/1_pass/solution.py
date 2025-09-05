import json
from copy import deepcopy

def zebra_solver():
    # Define categories and values
    categories = ["Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"]
    values = {
        "Name": ["Eric", "Peter", "Arnold", "Bob", "Alice"],
        "HouseStyle": ["modern", "craftsman", "ranch", "victorian", "colonial"],
        "Mother": ["Penny", "Kailyn", "Holly", "Janelle", "Aniya"],
        "PhoneModel": ["oneplus 9", "google pixel 6", "huawei p50", "iphone 13", "samsung galaxy s21"],
        "Drink": ["coffee", "water", "root beer", "tea", "milk"],
        "Animal": ["fish", "dog", "horse", "bird", "cat"],
    }

    # Initialize assignments per category; each is a list of 5 houses (index 0..4)
    cats = {cat: [None] * 5 for cat in categories}

    # Track used values per category to enforce uniqueness
    used = {cat: set() for cat in categories}

    # Helper: assign a value to (category, index)
    def assign(cats, used, cat, idx, val):
        # if already assigned, must match
        if cats[cat][idx] is not None and cats[cat][idx] != val:
            return False
        # uniqueness check
        if val in used[cat]:
            # Already used elsewhere
            existing_idx = cats[cat].index(val) if val in cats[cat] else None
            if existing_idx != idx:
                return False
        # assign
        cats[cat][idx] = val
        used[cat].add(val)
        return True

    # Helper: position of a value in a category
    def pos_of(cats, cat, val):
        try:
            return cats[cat].index(val)
        except ValueError:
            return None

    # Constraint checker: ensures no contradictions so far
    def check_constraints(cats):
        # 1. The person who uses a Google Pixel 6 is not in the first house.
        p0 = cats["PhoneModel"][0]
        if p0 is not None and p0 == "google pixel 6":
            return False

        # 2. The one who only drinks water is Alice.
        for i in range(5):
            n = cats["Name"][i]
            d = cats["Drink"][i]
            if n == "Alice" and d is not None and d != "water":
                return False
            if d == "water" and n is not None and n != "Alice":
                return False

        # 3. Colonial to the right of Huawei P50.
        cpos = pos_of(cats, "HouseStyle", "colonial")
        hpos = pos_of(cats, "PhoneModel", "huawei p50")
        if cpos is not None and hpos is not None and not (cpos > hpos):
            return False

        # 4. Horses <-> OnePlus 9.
        for i in range(5):
            a = cats["Animal"][i]
            p = cats["PhoneModel"][i]
            if a == "horse" and p is not None and p != "oneplus 9":
                return False
            if p == "oneplus 9" and a is not None and a != "horse":
                return False

        # 5. Ranch <-> Kailyn.
        for i in range(5):
            s = cats["HouseStyle"][i]
            m = cats["Mother"][i]
            if s == "ranch" and m is not None and m != "Kailyn":
                return False
            if m == "Kailyn" and s is not None and s != "ranch":
                return False

        # 6. Root beer <-> cat.
        for i in range(5):
            d = cats["Drink"][i]
            a = cats["Animal"][i]
            if d == "root beer" and a is not None and a != "cat":
                return False
            if a == "cat" and d is not None and d != "root beer":
                return False

        # 7. Colonial not in the fourth house (index 3).
        if cats["HouseStyle"][3] is not None and cats["HouseStyle"][3] == "colonial":
            return False

        # 8. Bird keeper is in the fourth house. (index 3)
        if cats["Animal"][3] is not None and cats["Animal"][3] != "bird":
            return False
        # If someone else assigned 'bird' not at index 3 -> invalid
        for i in range(5):
            if i != 3 and cats["Animal"][i] == "bird":
                return False

        # 9. Tea drinker is Bob.
        for i in range(5):
            n = cats["Name"][i]
            d = cats["Drink"][i]
            if n == "Bob" and d is not None and d != "tea":
                return False
            if d == "tea" and n is not None and n != "Bob":
                return False

        # 10. Tea drinker is somewhere to the right of mother Kailyn.
        teapos = pos_of(cats, "Drink", "tea")
        kpos = pos_of(cats, "Mother", "Kailyn")
        if teapos is not None and kpos is not None:
            if not (teapos > kpos):
                return False

        # 11. Root beer lover is somewhere to the left of mother Kailyn.
        rbpos = pos_of(cats, "Drink", "root beer")
        if rbpos is not None and kpos is not None:
            if not (rbpos < kpos):
                return False

        # 12. Horses <-> modern.
        for i in range(5):
            a = cats["Animal"][i]
            s = cats["HouseStyle"][i]
            if a == "horse" and s is not None and s != "modern":
                return False
            if s == "modern" and a is not None and a != "horse":
                return False

        # 13. iPhone 13 <-> milk.
        for i in range(5):
            p = cats["PhoneModel"][i]
            d = cats["Drink"][i]
            if p == "iphone 13" and d is not None and d != "milk":
                return False
            if d == "milk" and p is not None and p != "iphone 13":
                return False

        # 14. Dog <-> milk.
        for i in range(5):
            a = cats["Animal"][i]
            d = cats["Drink"][i]
            if a == "dog" and d is not None and d != "milk":
                return False
            if d == "milk" and a is not None and a != "dog":
                return False

        # 15. Google Pixel 6 <-> Craftsman.
        for i in range(5):
            p = cats["PhoneModel"][i]
            s = cats["HouseStyle"][i]
            if p == "google pixel 6" and s is not None and s != "craftsman":
                return False
            if s == "craftsman" and p is not None and p != "google pixel 6":
                return False

        # 16. Eric is not in the second house (index 1).
        if cats["Name"][1] is not None and cats["Name"][1] == "Eric":
            return False

        # 17. Tea drinker is in the fourth house (index 3).
        if cats["Drink"][3] is not None and cats["Drink"][3] != "tea":
            return False
        # If tea assigned elsewhere -> invalid
        for i in range(5):
            if i != 3 and cats["Drink"][i] == "tea":
                return False

        # 18. Horses are in the third house (index 2).
        if cats["Animal"][2] is not None and cats["Animal"][2] != "horse":
            return False
        for i in range(5):
            if i != 2 and cats["Animal"][i] == "horse":
                return False

        # 19. The person in a modern-style house is whose mother is Penny.
        for i in range(5):
            s = cats["HouseStyle"][i]
            m = cats["Mother"][i]
            if s == "modern" and m is not None and m != "Penny":
                return False
            if m == "Penny" and s is not None and s != "modern":
                return False

        # 20. Root beer lover is Peter.
        for i in range(5):
            d = cats["Drink"][i]
            n = cats["Name"][i]
            if d == "root beer" and n is not None and n != "Peter":
                return False
            if n == "Peter" and d is not None and d != "root beer":
                return False

        # 21. Mother Aniya is not in the fourth house (index 3).
        if cats["Mother"][3] is not None and cats["Mother"][3] == "Aniya":
            return False

        # 22. Mother Janelle is the one who only drinks water.
        for i in range(5):
            m = cats["Mother"][i]
            d = cats["Drink"][i]
            if m == "Janelle" and d is not None and d != "water":
                return False
            if d == "water" and m is not None and m != "Janelle":
                return False

        # Also from 2 and 22 combined: if mother is Janelle, name must be Alice; if drink water, name must be Alice.
        for i in range(5):
            m = cats["Mother"][i]
            d = cats["Drink"][i]
            n = cats["Name"][i]
            if m == "Janelle" and n is not None and n != "Alice":
                return False
            if d == "water" and n is not None and n != "Alice":
                return False
            if n == "Alice":
                if m is not None and m != "Janelle":
                    return False
                if d is not None and d != "water":
                    return False

        # Uniqueness check: no duplicates per category (except None)
        for cat in categories:
            seen = set()
            for val in cats[cat]:
                if val is None:
                    continue
                if val in seen:
                    return False
                seen.add(val)

        return True

    # Build dynamic domain for a slot
    def get_domain(cats, used, cat, idx):
        domain = [v for v in values[cat] if v not in used[cat]]

        # Apply local immediate domain reductions from other assigned slots in the same house.
        name = cats["Name"][idx]
        style = cats["HouseStyle"][idx]
        mother = cats["Mother"][idx]
        phone = cats["PhoneModel"][idx]
        drink = cats["Drink"][idx]
        animal = cats["Animal"][idx]

        # Fixed positions:
        if cat == "Animal":
            # clue 8: index 3 is bird
            if idx == 3:
                return ["bird"] if "bird" not in used["Animal"] or cats["Animal"][3] == "bird" else []
            # clue 18: index 2 is horse
            if idx == 2:
                return ["horse"] if "horse" not in used["Animal"] or cats["Animal"][2] == "horse" else []

        if cat == "Drink":
            # clue 17: index 3 is tea
            if idx == 3:
                return ["tea"] if "tea" not in used["Drink"] or cats["Drink"][3] == "tea" else []

        if cat == "Name":
            # Bob in the fourth due to tea and 9
            if idx == 3:
                return ["Bob"] if "Bob" not in used["Name"] or cats["Name"][3] == "Bob" else []
            # 16: Eric not in second (idx 1)
            if idx == 1 and "Eric" in domain:
                domain.remove("Eric")

        if cat == "PhoneModel":
            # 1: Pixel 6 not in first
            if idx == 0 and "google pixel 6" in domain:
                domain.remove("google pixel 6")
            # fixed: oneplus 9 at index 2 (from 18 and 4)
            if idx == 2:
                return ["oneplus 9"] if "oneplus 9" not in used["PhoneModel"] or cats["PhoneModel"][2] == "oneplus 9" else []
            # fixed: google pixel 6 at index 3 (from 15 and 17/8 gave Craftsman)
            if idx == 3:
                return ["google pixel 6"] if "google pixel 6" not in used["PhoneModel"] or cats["PhoneModel"][3] == "google pixel 6" else []

        if cat == "HouseStyle":
            # fixed modern at index 2 (18/12)
            if idx == 2:
                return ["modern"] if "modern" not in used["HouseStyle"] or cats["HouseStyle"][2] == "modern" else []
            # fixed craftsman at index 3 (15 with Pixel 6 at 4th)
            if idx == 3:
                return ["craftsman"] if "craftsman" not in used["HouseStyle"] or cats["HouseStyle"][3] == "craftsman" else []
            # 7: Colonial not at index 3 already handled
            pass

        if cat == "Mother":
            # fixed Penny at index 2 (19)
            if idx == 2:
                return ["Penny"] if "Penny" not in used["Mother"] or cats["Mother"][2] == "Penny" else []
            # 21: Aniya not at index 3
            if idx == 3 and "Aniya" in domain:
                domain.remove("Aniya")

        # Cross-links at this house to narrow domain
        # water -> Alice, Janelle
        if cat == "Drink":
            if name == "Alice":
                domain = [v for v in domain if v == "water"]
            if mother == "Janelle":
                domain = [v for v in domain if v == "water"]
            if name == "Bob":
                domain = [v for v in domain if v == "tea"]
            if animal == "cat":
                domain = [v for v in domain if v == "root beer"]
            if phone == "iphone 13":
                domain = [v for v in domain if v == "milk"]
            if animal == "dog":
                domain = [v for v in domain if v == "milk"]
        elif cat == "Name":
            if drink == "water":
                domain = [v for v in domain if v == "Alice"]
            if drink == "tea":
                domain = [v for v in domain if v == "Bob"]
            if drink == "root beer":
                domain = [v for v in domain if v == "Peter"]
        elif cat == "Mother":
            if drink == "water":
                domain = [v for v in domain if v == "Janelle"]
            if style == "ranch":
                domain = [v for v in domain if v == "Kailyn"]
            if style == "modern":
                domain = [v for v in domain if v == "Penny"]
        elif cat == "HouseStyle":
            if mother == "Kailyn":
                domain = [v for v in domain if v == "ranch"]
            if mother == "Penny":
                domain = [v for v in domain if v == "modern"]
            if phone == "google pixel 6":
                domain = [v for v in domain if v == "craftsman"]
            if animal == "horse":
                domain = [v for v in domain if v == "modern"]
            # Additionally, if index == 3, colonial already excluded by position fix.
        elif cat == "PhoneModel":
            if style == "craftsman":
                domain = [v for v in domain if v == "google pixel 6"]
            if animal == "horse":
                domain = [v for v in domain if v == "oneplus 9"]
            if drink == "milk":
                domain = [v for v in domain if v == "iphone 13"]
        elif cat == "Animal":
            if drink == "root beer":
                domain = [v for v in domain if v == "cat"]
            if phone == "oneplus 9":
                domain = [v for v in domain if v == "horse"]
            if style == "modern":
                domain = [v for v in domain if v == "horse"]
            if drink == "milk":
                domain = [v for v in domain if v == "dog"]

        # Remove any values that would immediately violate constraints with current partial
        filtered = []
        for v in domain:
            # Try temporary assign and check
            cats_tmp = cats
            used_tmp = used
            # We won't mutate original in this preview; just check logically.
            # Minimal local check: we rely on full check after actual assignment; for domain we keep as is.
            filtered.append(v)
        return filtered

    # Pre-assign facts from clues for immediate pruning:
    # 8: Bird at house 4 (index 3)
    assign(cats, used, "Animal", 3, "bird")
    # 17 + 9: Tea at house 4, and tea drinker is Bob
    assign(cats, used, "Drink", 3, "tea")
    assign(cats, used, "Name", 3, "Bob")
    # 18: Horses in 3rd house (index 2)
    assign(cats, used, "Animal", 2, "horse")
    # 12: Horses <-> modern
    assign(cats, used, "HouseStyle", 2, "modern")
    # 4: Horses <-> OnePlus 9
    assign(cats, used, "PhoneModel", 2, "oneplus 9")
    # 19: Modern -> Penny (mother)
    assign(cats, used, "Mother", 2, "Penny")
    # 15: Pixel 6 <-> Craftsman, and since we know tea house is 4th (and Pixel 6 not 1st), deduce Craftsman is at 4th because 15 binds model to style. We assign both sides for 4th.
    assign(cats, used, "PhoneModel", 3, "google pixel 6")
    assign(cats, used, "HouseStyle", 3, "craftsman")

    # Backtracking solver
    slots = [(cat, idx) for cat in categories for idx in range(5)]

    def is_complete(cats):
        return all(cats[cat][i] is not None for cat in categories for i in range(5))

    def select_unassigned_variable(cats, used):
        # Minimum Remaining Values heuristic
        best = None
        best_domain = None
        for cat, idx in slots:
            if cats[cat][idx] is None:
                domain = get_domain(cats, used, cat, idx)
                if best is None or len(domain) < len(best_domain):
                    best = (cat, idx)
                    best_domain = domain
                # Early fail
                if len(domain) == 0:
                    return (cat, idx), []
        return best, best_domain

    def backtrack(cats, used):
        if not check_constraints(cats):
            return None
        if is_complete(cats):
            if check_constraints(cats):
                return cats
            return None

        (cat, idx), domain = select_unassigned_variable(cats, used)
        if domain is None:
            return None
        for val in domain:
            # Copy state
            cats2 = deepcopy(cats)
            used2 = deepcopy(used)
            if not assign(cats2, used2, cat, idx, val):
                continue
            if not check_constraints(cats2):
                continue
            result = backtrack(cats2, used2)
            if result is not None:
                return result
        return None

    solution = backtrack(cats, used)
    if solution is None:
        raise RuntimeError("No solution found")

    # Build JSON output
    header = ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"]
    rows = []
    for i in range(5):
        row = [
            str(i + 1),
            solution["Name"][i],
            solution["HouseStyle"][i],
            solution["Mother"][i],
            solution["PhoneModel"][i],
            solution["Drink"][i],
            solution["Animal"][i],
        ]
        rows.append(row)

    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = zebra_solver()
    print(json.dumps(result, ensure_ascii=False))