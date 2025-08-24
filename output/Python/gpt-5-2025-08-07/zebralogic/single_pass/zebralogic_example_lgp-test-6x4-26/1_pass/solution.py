import itertools
import json

def solve():
    houses = [1, 2, 3, 4, 5, 6]

    Names = ["Peter", "Bob", "Carol", "Eric", "Alice", "Arnold"]
    Pets = ["bird", "dog", "cat", "rabbit", "fish", "hamster"]
    Styles = ["victorian", "ranch", "modern", "mediterranean", "colonial", "craftsman"]
    Months = ["mar", "sept", "may", "feb", "jan", "april"]

    # Helper to invert mapping value->house
    def index_of(mapping, value):
        for h, v in mapping.items():
            if v == value:
                return h
        return None

    # Generate name assignments using given constraints:
    # - Peter in house 2
    # - Carol in house 3
    # - Eric in house 6
    # - Arnold in house 4
    # The remaining names (Bob, Alice) go to houses 1 and 5 in either order
    def gen_name_maps():
        base = {2: "Peter", 3: "Carol", 4: "Arnold", 6: "Eric"}
        remaining_names = [n for n in Names if n not in base.values()]  # ["Bob", "Alice"]
        remaining_houses = [1, 5]
        for perm in itertools.permutations(remaining_names, len(remaining_houses)):
            m = dict(base)
            for h, n in zip(remaining_houses, perm):
                m[h] = n
            yield m

    # Generate month assignments using constraints:
    # 3. May is in the second house.
    # 5 & 17. Carol is in the third house and is March.
    # 2. January is somewhere to the left of September.
    # 15. January is directly left of April.
    def gen_month_maps():
        base = {2: "may", 3: "mar"}
        # Try all positions for the Jan-April adjacent pair
        results = []
        for jan_pos in range(1, 6):
            apr_pos = jan_pos + 1
            if jan_pos in base or apr_pos in base:
                continue  # cannot place Jan/Apr where already fixed
            months = dict(base)
            months[jan_pos] = "jan"
            months[apr_pos] = "april"
            # Remaining months to place: {"sept", "feb"} on remaining houses
            remaining_houses = [h for h in houses if h not in months]
            remaining_months = ["sept", "feb"]
            for perm in itertools.permutations(remaining_months, 2):
                mm = dict(months)
                for h, m in zip(remaining_houses, perm):
                    mm[h] = m
                # Check constraint 2: Jan left of Sept
                if index_of(mm, "jan") < index_of(mm, "sept"):
                    results.append(mm)
        return results

    # Generate style assignments using constraints:
    # 4. Colonial is in the second house.
    # 18. Craftsman is in the fourth house.
    # 6. Mediterranean is not in the sixth house.
    # 12. Colonial (house 2) is somewhere to the left of Modern -> Modern must be at a house > 2.
    def gen_style_maps():
        base = {2: "colonial", 4: "craftsman"}
        remaining_houses = [h for h in houses if h not in base]
        remaining_styles = [s for s in Styles if s not in base.values()]
        for perm in itertools.permutations(remaining_styles, len(remaining_houses)):
            styles = dict(base)
            ok = True
            for h, s in zip(remaining_houses, perm):
                styles[h] = s
            # Constraint 6: Mediterranean not in sixth
            if styles[6] == "mediterranean":
                ok = False
            # Constraint 12: Modern must be to the right of house 2
            if index_of(styles, "modern") is None or index_of(styles, "modern") <= 2:
                ok = False
            if ok:
                yield styles

    # Find pet assignments using constraints:
    # 19. Dog at house 4.
    # 1. Hamster right of March.
    # 10. There are two houses between Victorian and Hamster (abs difference = 3).
    # 16. One house between Bird and Modern (abs difference = 2).
    # 9. One house between Cat and Victorian (abs difference = 2).
    # 7. Fish is somewhere to the right of Bob.
    # 13. Fish not in the second house.
    def find_pet_assignment(names_map, months_map, styles_map):
        i_mar = index_of(months_map, "mar")
        i_modern = index_of(styles_map, "modern")
        i_victorian = index_of(styles_map, "victorian")
        i_bob = index_of(names_map, "Bob")

        # Domains for each pet
        domains = {}

        # Dog fixed at house 4
        domains["dog"] = {4}

        # Hamster: to right of March and 3 apart from Victorian
        hamster_candidates = set(h for h in houses if h > i_mar)
        if i_victorian is not None:
            hamster_candidates &= {i_victorian - 3, i_victorian + 3}
        hamster_candidates &= set(houses)
        domains["hamster"] = hamster_candidates

        # Bird: exactly two apart from Modern
        bird_candidates = set()
        if i_modern is not None:
            for d in (-2, 2):
                pos = i_modern + d
                if 1 <= pos <= 6:
                    bird_candidates.add(pos)
        domains["bird"] = bird_candidates

        # Cat: exactly two apart from Victorian
        cat_candidates = set()
        if i_victorian is not None:
            for d in (-2, 2):
                pos = i_victorian + d
                if 1 <= pos <= 6:
                    cat_candidates.add(pos)
        domains["cat"] = cat_candidates

        # Fish: somewhere to the right of Bob, and not in house 2
        fish_candidates = set(h for h in houses if h > i_bob and h != 2)
        domains["fish"] = fish_candidates

        # Rabbit: no direct positional constraints
        domains["rabbit"] = set(houses)

        # Remove impossible positions where dog is at 4 (no other pet can be at 4)
        for pet in domains:
            if pet != "dog":
                domains[pet] -= {4}

        # Backtracking to assign each pet to a unique house
        pets_order = sorted(Pets, key=lambda p: len(domains[p]))  # try smallest domains first

        assignment = {}

        def backtrack(idx, used_houses):
            if idx == len(pets_order):
                return True
            pet = pets_order[idx]
            for h in sorted(domains[pet]):
                if h in used_houses:
                    continue
                assignment[pet] = h
                # Early consistency checks already encoded in domains; proceed
                if backtrack(idx + 1, used_houses | {h}):
                    return True
                del assignment[pet]
            return False

        possible = all(len(domains[p]) > 0 for p in Pets)
        if not possible:
            return None

        if backtrack(0, set()):
            return assignment
        return None

    solutions = []

    for name_map in gen_name_maps():
        # Validate name-specific constraints already guaranteed by generator
        # Now generate month maps
        for month_map in gen_month_maps():
            # Basic check of fixed month constraints (already handled)
            # Generate style maps
            for style_map in gen_style_maps():
                # Check linkage constraints between names and styles:
                # 11. Craftsman is Arnold -> ensured by fixed house 4 assignments
                # 14. Peter is Colonial -> ensured by fixed house 2 assignments
                # Now find pet assignment under all constraints
                pet_map = find_pet_assignment(name_map, month_map, style_map)
                if pet_map is None:
                    continue

                # Verify all clues holistically (redundant but ensures everything)
                def house_of(category_map, value):
                    return index_of(category_map, value)

                # 1
                if house_of(pet_map, "hamster") <= house_of(month_map, "mar"):
                    continue
                # 2
                if house_of(month_map, "jan") >= house_of(month_map, "sept"):
                    continue
                # 3
                if month_map[2] != "may":
                    continue
                # 4
                if style_map[2] != "colonial":
                    continue
                # 5
                if name_map[3] != "Carol":
                    continue
                # 6
                if style_map[6] == "mediterranean":
                    continue
                # 7
                if house_of(pet_map, "fish") <= house_of(name_map, "Bob"):
                    continue
                # 8
                if name_map[6] != "Eric":
                    continue
                # 9
                if abs(house_of(pet_map, "cat") - house_of(style_map, "victorian")) != 2:
                    continue
                # 10
                if abs(house_of(style_map, "victorian") - house_of(pet_map, "hamster")) != 3:
                    continue
                # 11
                if name_map[4] != "Arnold" or style_map[4] != "craftsman":
                    continue
                # 12
                if house_of(style_map, "colonial") >= house_of(style_map, "modern"):
                    continue
                # 13
                if house_of(pet_map, "fish") == 2:
                    continue
                # 14
                if name_map[2] != "Peter" or style_map[2] != "colonial":
                    continue
                # 15
                if not (house_of(month_map, "jan") + 1 == house_of(month_map, "april")):
                    continue
                # 16
                if abs(house_of(pet_map, "bird") - house_of(style_map, "modern")) != 2:
                    continue
                # 17
                if month_map[3] != "mar":
                    continue
                # 18
                if style_map[4] != "craftsman":
                    continue
                # 19
                if pet_map[4] != "dog":
                    continue

                # Found a valid solution
                solutions.append((name_map, pet_map, style_map, month_map))

    # Ensure we found exactly one solution
    if not solutions:
        raise RuntimeError("No solution found")
    # If multiple, take the first; puzzle should be unique
    name_map, pet_map, style_map, month_map = solutions[0]

    # Build output JSON structure
    header = ["House", "Name", "Pet", "HouseStyle", "Birthday"]
    rows = []
    for h in houses:
        rows.append([
            str(h),
            name_map[h],
            pet_map[h],
            style_map[h],
            month_map[h]
        ])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve()