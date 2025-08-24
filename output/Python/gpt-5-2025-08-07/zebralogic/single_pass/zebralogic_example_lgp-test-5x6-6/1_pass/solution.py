import json
import itertools

def solve():
    houses = [0,1,2,3,4]  # 0-based indices for houses 1..5

    categories = ["Name", "Vacation", "Education", "Color", "Phone", "Food"]

    items = {
        "Name": ["Arnold", "Eric", "Alice", "Bob", "Peter"],
        "Vacation": ["mountain", "city", "cruise", "beach", "camping"],
        "Education": ["doctorate", "high school", "bachelor", "associate", "master"],
        "Color": ["blue", "red", "white", "yellow", "green"],
        "Phone": ["google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"],
        "Food": ["grilled cheese", "stir fry", "pizza", "spaghetti", "stew"],
    }

    # Helper to get position of an item in a category if that category is assigned
    def pos(assignments, cat, item):
        if cat not in assignments:
            return None
        return assignments[cat].index(item)

    # Constraint checker for current partial assignment
    def check(assignments):
        # 1. The person who loves the stew is not in the first house.
        if "Food" in assignments:
            if assignments["Food"][0] == "stew":
                return False

        # 2. There are two houses between stir fry and associate (diff 3)
        p_sf = pos(assignments, "Food", "stir fry")
        p_assoc = pos(assignments, "Education", "associate")
        if p_sf is not None and p_assoc is not None:
            if abs(p_sf - p_assoc) != 3:
                return False

        # 3. mountain = bachelor
        p_mtn = pos(assignments, "Vacation", "mountain")
        p_bach = pos(assignments, "Education", "bachelor")
        if p_mtn is not None and p_bach is not None:
            if p_mtn != p_bach:
                return False

        # 4. doctorate to right of Bob
        p_doc = pos(assignments, "Education", "doctorate")
        p_bob = pos(assignments, "Name", "Bob")
        if p_doc is not None and p_bob is not None:
            if not (p_doc > p_bob):
                return False

        # 5. S21 is in the third house (index 2)
        if "Phone" in assignments:
            if assignments["Phone"][2] != "samsung galaxy s21":
                return False

        # 6. Eric is the doctorate
        p_eric = pos(assignments, "Name", "Eric")
        if p_eric is not None and p_doc is not None:
            if p_eric != p_doc:
                return False

        # 7. doctorate is in the third house
        if "Education" in assignments:
            if assignments["Education"][2] != "doctorate":
                return False

        # 8. stir fry = bachelor
        p_sf = pos(assignments, "Food", "stir fry")
        if p_sf is not None and p_bach is not None:
            if p_sf != p_bach:
                return False

        # 9. doctorate = pizza
        p_pizza = pos(assignments, "Food", "pizza")
        if p_pizza is not None and p_doc is not None:
            if p_pizza != p_doc:
                return False

        # 10. green to the right of Peter
        p_green = pos(assignments, "Color", "green")
        p_peter = pos(assignments, "Name", "Peter")
        if p_green is not None and p_peter is not None:
            if not (p_green > p_peter):
                return False

        # 11. camping = iPhone 13
        p_camp = pos(assignments, "Vacation", "camping")
        p_iphone = pos(assignments, "Phone", "iphone 13")
        if p_camp is not None and p_iphone is not None:
            if p_camp != p_iphone:
                return False

        # 12. cruise = Alice
        p_cruise = pos(assignments, "Vacation", "cruise")
        p_alice = pos(assignments, "Name", "Alice")
        if p_cruise is not None and p_alice is not None:
            if p_cruise != p_alice:
                return False

        # 13. one house between high school and S21 (diff 2)
        p_hs = pos(assignments, "Education", "high school")
        p_s21 = pos(assignments, "Phone", "samsung galaxy s21")
        if p_hs is not None and p_s21 is not None:
            if abs(p_hs - p_s21) != 2:
                return False

        # 14. Google Pixel 6 = Arnold
        p_pixel = pos(assignments, "Phone", "google pixel 6")
        p_arnold = pos(assignments, "Name", "Arnold")
        if p_pixel is not None and p_arnold is not None:
            if p_pixel != p_arnold:
                return False

        # 15. OnePlus 9 right of Huawei P50
        p_op9 = pos(assignments, "Phone", "oneplus 9")
        p_huawei = pos(assignments, "Phone", "huawei p50")
        if p_op9 is not None and p_huawei is not None:
            if not (p_op9 > p_huawei):
                return False

        # 16. Arnold = grilled cheese
        p_gc = pos(assignments, "Food", "grilled cheese")
        if p_gc is not None and p_arnold is not None:
            if p_gc != p_arnold:
                return False

        # 17. grilled cheese not in fourth house (index 3)
        if "Food" in assignments:
            if assignments["Food"][3] == "grilled cheese":
                return False

        # 18. two houses between bachelor and red (diff 3)
        p_red = pos(assignments, "Color", "red")
        if p_bach is not None and p_red is not None:
            if abs(p_bach - p_red) != 3:
                return False

        # 19. beach right of city
        p_beach = pos(assignments, "Vacation", "beach")
        p_city = pos(assignments, "Vacation", "city")
        if p_beach is not None and p_city is not None:
            if not (p_beach > p_city):
                return False

        # 20. green not in second house (index 1)
        if "Color" in assignments:
            if assignments["Color"][1] == "green":
                return False

        # 21. blue to the right of Peter
        p_blue = pos(assignments, "Color", "blue")
        if p_blue is not None and p_peter is not None:
            if not (p_blue > p_peter):
                return False

        # 22. one house between camping and yellow (diff 2)
        p_yellow = pos(assignments, "Color", "yellow")
        if p_camp is not None and p_yellow is not None:
            if abs(p_camp - p_yellow) != 2:
                return False

        # Derived implications we can safely enforce to prune early:
        # Peter cannot be in 4th or 5th house because both blue and green must be to his right.
        if "Name" in assignments:
            p_peter = assignments["Name"].index("Peter")
            if p_peter >= 3:
                return False

        # Arnold cannot be in 4th house because grilled cheese is not in 4th and Arnold=grilled cheese.
        if "Name" in assignments:
            if assignments["Name"][3] == "Arnold":
                return False

        # Bob must be left of doctorate which is at index 2 -> Bob in 0 or 1
        if "Name" in assignments:
            if assignments["Name"].index("Bob") >= 2:
                return False

        # Eric must be at index 2
        if "Name" in assignments:
            if assignments["Name"][2] != "Eric":
                return False

        # Education fixed: doctorate at index 2, high school at index 0 or 4, bachelor != 2, and associate diff 3 from bachelor
        if "Education" in assignments:
            edu = assignments["Education"]
            if edu[2] != "doctorate":
                return False
            if edu.index("high school") not in (0,4):
                return False
            if edu.index("bachelor") == 2:
                return False
            if abs(edu.index("associate") - edu.index("bachelor")) != 3:
                return False

        # Food fixed: pizza at 2, grilled cheese not at 3, stew not at 0
        if "Food" in assignments:
            food = assignments["Food"]
            if food[2] != "pizza":
                return False
            if food[3] == "grilled cheese":
                return False
            if food[0] == "stew":
                return False

        # Phone fixed: s21 at 2
        if "Phone" in assignments:
            phone = assignments["Phone"]
            if phone[2] != "samsung galaxy s21":
                return False

        # Color fixed: green not at index 1
        if "Color" in assignments:
            if assignments["Color"][1] == "green":
                return False

        return True

    # Generate candidate permutations for a category with some intrinsic pruning
    def candidates_for_category(cat):
        all_items = items[cat]
        perms = itertools.permutations(all_items)
        for perm in perms:
            # Intrinsic filters per category
            if cat == "Education":
                if perm[2] != "doctorate":
                    continue
                # high school must be index 0 or 4 due to rule 13 and phone s21 fixed at index 2
                if perm.index("high school") not in (0,4):
                    continue
                if perm.index("bachelor") == 2:
                    continue
                # also enforce associate diff 3 from bachelor within category
                if abs(perm.index("associate") - perm.index("bachelor")) != 3:
                    continue
            elif cat == "Phone":
                if perm[2] != "samsung galaxy s21":
                    continue
                # OnePlus 9 right of Huawei P50 can be pre-filtered within the category
                if not (perm.index("oneplus 9") > perm.index("huawei p50")):
                    continue
            elif cat == "Food":
                if perm[2] != "pizza":
                    continue
                if perm[3] == "grilled cheese":
                    continue
                if perm[0] == "stew":
                    continue
            elif cat == "Name":
                if perm[2] != "Eric":
                    continue
                # Bob must be in 0 or 1
                if perm.index("Bob") >= 2:
                    continue
                # Peter cannot be in 3 or 4 (needs two colors to the right)
                if perm.index("Peter") >= 3:
                    continue
                # Arnold cannot be in 3 (fourth house)
                if perm[3] == "Arnold":
                    continue
            elif cat == "Color":
                # green not in second house
                if perm[1] == "green":
                    continue
            # no intrinsic filter for Vacation other than later cross-constraints
            yield list(perm)

    # Choose order to assign categories to maximize pruning
    order = ["Education", "Phone", "Food", "Name", "Vacation", "Color"]

    solution_assignments = None

    def backtrack(assignments, idx):
        nonlocal solution_assignments
        if solution_assignments is not None:
            return
        if idx == len(order):
            if check(assignments):
                solution_assignments = {k: v[:] for k, v in assignments.items()}
            return
        cat = order[idx]
        for cand in candidates_for_category(cat):
            assignments[cat] = cand
            if check(assignments):
                backtrack(assignments, idx + 1)
                if solution_assignments is not None:
                    return
            del assignments[cat]

    backtrack({}, 0)
    if solution_assignments is None:
        raise RuntimeError("No solution found.")

    # Build output rows
    rows = []
    for i in range(5):
        house_num = str(i+1)
        name = solution_assignments["Name"][i]
        vacation = solution_assignments["Vacation"][i]
        education = solution_assignments["Education"][i]
        color = solution_assignments["Color"][i]
        phone = solution_assignments["Phone"][i]
        food = solution_assignments["Food"][i]
        rows.append([house_num, name, vacation, education, color, phone, food])

    output = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))