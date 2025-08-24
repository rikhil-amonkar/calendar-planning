import json
from itertools import permutations

def invert_list(lst):
    return {v: i for i, v in enumerate(lst)}

def solve():
    houses = [0,1,2,3,4,5]  # 0-based indices for houses 1..6

    Names = ["Arnold", "Carol", "Peter", "Eric", "Bob", "Alice"]
    Styles = ["ranch", "colonial", "modern", "craftsman", "mediterranean", "victorian"]
    Foods = ["pizza", "stew", "spaghetti", "grilled cheese", "stir fry", "soup"]
    Vacations = ["cultural", "cruise", "mountain", "camping", "city", "beach"]
    Heights = ["average", "very tall", "very short", "short", "tall", "super tall"]
    Cigars = ["yellow monster", "prince", "dunhill", "pall mall", "blue master", "blends"]

    # Fixed positions by clues:
    # 1. Alice is in the fifth house. -> index 4
    # 9. Eric is in the fourth house. -> index 3

    fixed_names = {4: "Alice", 3: "Eric"}
    remaining_house_indices = [i for i in houses if i not in fixed_names]
    remaining_names = [n for n in Names if n not in fixed_names.values()]

    for perm_names in permutations(remaining_names):
        name_at = [None]*6
        name_at[4] = "Alice"
        name_at[3] = "Eric"
        for idx, house_idx in enumerate(remaining_house_indices):
            name_at[house_idx] = perm_names[idx]
        pos_name = invert_list(name_at)

        # 17. Stir fry directly left of Bob -> Bob not at house 1 (index 0)
        if pos_name["Bob"] == 0:
            continue

        # Food assignments
        # 3 and 14 imply Alice eats spaghetti; 1 gives Alice at 5 => food[4] = spaghetti
        # 4. Arnold eats stew
        # 17. Stir fry is directly left of Bob
        # 5. There is one house between average height (stir fry person) and Peter
        # Create base food array
        bob_pos = pos_name["Bob"]
        peter_pos = pos_name["Peter"]
        arnold_pos = pos_name["Arnold"]

        sf_pos = bob_pos - 1  # stir fry position
        # Check stir fry position valid and not conflicting with spaghetti at 4 (index 4)
        if sf_pos < 0 or sf_pos >= 6 or sf_pos == 4:
            continue
        # Check one house between stir fry (average) and Peter
        if abs(sf_pos - peter_pos) != 2:
            continue

        food_at = [None]*6
        food_at[4] = "spaghetti"
        # Arnold eats stew; ensure no conflict
        if arnold_pos == 4:
            continue
        food_at[arnold_pos] = "stew"
        # Set stir fry
        if food_at[sf_pos] is not None:
            continue
        food_at[sf_pos] = "stir fry"

        # Fill remaining foods
        remaining_foods = [f for f in Foods if f not in food_at]
        remaining_positions = [i for i in houses if food_at[i] is None]

        for perm_foods in permutations(remaining_foods):
            fa = food_at[:]
            ok_food = True
            for i, pos in enumerate(remaining_positions):
                if fa[pos] is not None:
                    ok_food = False
                    break
                fa[pos] = perm_foods[i]
            if not ok_food:
                continue

            pos_food = invert_list(fa)
            # We will use grilled cheese position for later height constraint
            gc_pos = pos_food["grilled cheese"]

            # Style assignments
            # 14 => Victorian at Alice's house (5th -> index 4)
            # 2 => colonial = stir fry
            # 6 => craftsman not at index 2 (house 3)
            # 18 => modern somewhere left of Alice (index < 4)
            # 19 => craftsman somewhere to the left of short (thus craftsman not at index 5)
            # 15/8/22/16 affect ranch relative to tall, etc., ranch must be left of Victorian because tall is left of Victorian
            style_at = [None]*6
            style_at[4] = "victorian"
            # colonial at stir fry position
            if style_at[sf_pos] is not None:
                continue
            style_at[sf_pos] = "colonial"

            remaining_styles = [s for s in Styles if s not in style_at]
            remaining_positions_s = [i for i in houses if style_at[i] is None]

            # We'll permute remaining styles with constraints:
            def style_allowed(style, pos):
                # craftsman not at index 2 (house 3) and not at index 5 (house 6)
                if style == "craftsman" and pos in (2,5):
                    return False
                # modern must be in positions < 4
                if style == "modern" and pos >= 4:
                    return False
                # ranch must be left of Victorian (since tall left of Victorian and tall=ranch) => pos < 4
                if style == "ranch" and not (pos < 4):
                    return False
                # ranch cannot be at 0 because blends must be left of blue master (23)
                if style == "ranch" and pos == 0:
                    return False
                # colonial already set at sf_pos; ensure consistency
                if style == "colonial":
                    return False
                # victorian already set at 4
                if style == "victorian":
                    return False
                return True

            def generate_style_arrangements():
                for perm_styles in permutations(remaining_styles):
                    sa = style_at[:]
                    good = True
                    for sty, pos in zip(perm_styles, remaining_positions_s):
                        if not style_allowed(sty, pos):
                            good = False
                            break
                        sa[pos] = sty
                    if not good:
                        continue
                    yield sa

            for sa in generate_style_arrangements():
                pos_style = invert_list(sa)
                # Height assignments
                # 7 => average = stir fry
                # 15 => tall = beach (vac later), tall is somewhere to the left of Victorian (16) => tall in indices 0..3
                # 21 => grilled cheese two houses between super tall => distance 3
                height_at = [None]*6
                height_at[sf_pos] = "average"

                # Determine possible super tall positions based on grilled cheese
                st_candidates = []
                if gc_pos - 3 >= 0:
                    st_candidates.append(gc_pos - 3)
                if gc_pos + 3 < 6:
                    st_candidates.append(gc_pos + 3)
                # Remove if conflicts with average position
                st_candidates = [p for p in st_candidates if height_at[p] is None]
                if not st_candidates:
                    continue

                # craftsman < short must be checked after both assigned
                craftsman_pos = pos_style["craftsman"]

                for st_pos in st_candidates:
                    ha0 = height_at[:]
                    ha0[st_pos] = "super tall"

                    # Choose tall position (must be in 0..3 and free)
                    for tall_pos in [i for i in range(4) if ha0[i] is None]:
                        ha1 = ha0[:]
                        ha1[tall_pos] = "tall"

                        # Remaining height values: "very tall", "very short", "short"
                        remaining_heights = [h for h in Heights if h not in ha1]
                        remaining_positions_h = [i for i in houses if ha1[i] is None]
                        for perm_heights in permutations(remaining_heights):
                            ha = ha1[:]
                            good_h = True
                            for h, pos in zip(perm_heights, remaining_positions_h):
                                ha[pos] = h
                            # Check craftsman left of short (19)
                            short_pos = ha.index("short")
                            if not (craftsman_pos < short_pos):
                                good_h = False
                            # Tall must be left of Victorian (16) -> ensured by selection in 0..3
                            if not good_h:
                                continue

                            pos_height = invert_list(ha)

                            # Vacations
                            # 12 => mountain = very tall
                            # 11 => mountain smoker uses yellow monster; handle in cigars
                            # 8 => beach = ranch (in styles)
                            # 15 => tall = beach (vacation)
                            # 10 => colonial and camping with one in between => distance 2
                            # 24 => cultural = pizza
                            # 25 => pizza left of cruise
                            vac_at = [None]*6

                            pos_mountain = pos_height["very tall"]
                            vac_at[pos_mountain] = "mountain"

                            pos_beach = pos_height["tall"]
                            # Beach must equal ranch style position; enforce later after style known
                            vac_at[pos_beach] = "beach"

                            pos_cultural = pos_food["pizza"]
                            # Cannot assign two vacation values to same house
                            if vac_at[pos_cultural] is not None and vac_at[pos_cultural] != "cultural":
                                continue
                            vac_at[pos_cultural] = "cultural"

                            # Camping at colonial +/- 2
                            colonial_pos = pos_style["colonial"]
                            camp_candidates = []
                            if colonial_pos - 2 >= 0:
                                camp_candidates.append(colonial_pos - 2)
                            if colonial_pos + 2 < 6:
                                camp_candidates.append(colonial_pos + 2)

                            for camp_pos in camp_candidates:
                                va0 = vac_at[:]
                                # Check conflicts
                                if va0[camp_pos] is not None and va0[camp_pos] != "camping":
                                    continue
                                va0[camp_pos] = "camping"

                                # Now enforce that beach aligns with ranch
                                if pos_style["ranch"] != pos_beach:
                                    continue

                                # Remaining vacations: "cruise", "city"
                                used_vac_values = [v for v in va0 if v is not None]
                                remaining_vacs = [v for v in Vacations if v not in used_vac_values]
                                remaining_positions_v = [i for i in houses if va0[i] is None]
                                if len(remaining_vacs) != 2 or len(remaining_positions_v) != 2:
                                    continue

                                # Assign the remaining two vacations in both possible ways checking pizza left of cruise
                                for perm_vacs in permutations(remaining_vacs):
                                    va = va0[:]
                                    for v, pos in zip(perm_vacs, remaining_positions_v):
                                        va[pos] = v
                                    pos_vac = invert_list(va)
                                    # 25 => pizza (cultural) left of cruise
                                    if not (pos_vac["cultural"] < pos_vac["cruise"]):
                                        continue

                                    # Cigars
                                    # 22 => ranch = blue master
                                    # 23 => blends directly left of blue master
                                    # 11 => mountain = yellow monster
                                    # 13 => mountain and dunhill are next to each other
                                    # 20 => stir fry left of prince
                                    cigar_at = [None]*6
                                    pos_ranch = pos_style["ranch"]

                                    # Blue Master at ranch; blends immediately left
                                    if pos_ranch == 0:
                                        continue
                                    cigar_at[pos_ranch] = "blue master"
                                    left_of_ranch = pos_ranch - 1
                                    if cigar_at[left_of_ranch] is not None:
                                        continue
                                    cigar_at[left_of_ranch] = "blends"

                                    # Yellow Monster at mountain
                                    pos_mountain = pos_vac["mountain"]
                                    if cigar_at[pos_mountain] is not None and cigar_at[pos_mountain] != "yellow monster":
                                        continue
                                    cigar_at[pos_mountain] = "yellow monster"

                                    # Dunhill adjacent to mountain
                                    dunhill_candidates = []
                                    if pos_mountain - 1 >= 0:
                                        dunhill_candidates.append(pos_mountain - 1)
                                    if pos_mountain + 1 < 6:
                                        dunhill_candidates.append(pos_mountain + 1)

                                    for dun_pos in dunhill_candidates:
                                        ca0 = cigar_at[:]
                                        if ca0[dun_pos] is not None and ca0[dun_pos] != "dunhill":
                                            continue
                                        if ca0[dun_pos] is None:
                                            ca0[dun_pos] = "dunhill"

                                        # Prince must be to the right of stir fry
                                        prince_candidates = [i for i in houses if i > sf_pos and ca0[i] is None]
                                        if not prince_candidates:
                                            continue
                                        for pr_pos in prince_candidates:
                                            ca1 = ca0[:]
                                            ca1[pr_pos] = "prince"

                                            # Pall Mall goes to remaining empty slot
                                            remaining_cigar_positions = [i for i in houses if ca1[i] is None]
                                            if len(remaining_cigar_positions) != 1:
                                                continue
                                            ca1[remaining_cigar_positions[0]] = "pall mall"

                                            pos_cigar = invert_list(ca1)

                                            # Final cross-checks (redundant but safe)
                                            # 13 mountain and Dunhill next to each other
                                            if abs(pos_cigar["dunhill"] - pos_vac["mountain"]) != 1:
                                                continue
                                            # 20 stir fry left of Prince
                                            if not (sf_pos < pos_cigar["prince"]):
                                                continue
                                            # 23 blends directly left of blue master
                                            if not (pos_cigar["blends"] + 1 == pos_cigar["blue master"]):
                                                continue
                                            # 22 ranch = blue master
                                            if not (pos_style["ranch"] == pos_cigar["blue master"]):
                                                continue
                                            # 11 yellow monster at mountain
                                            if not (pos_cigar["yellow monster"] == pos_vac["mountain"]):
                                                continue
                                            # 10 colonial and camping distance 2
                                            if abs(pos_style["colonial"] - pos_vac["camping"]) != 2:
                                                continue
                                            # 7 average = stir fry
                                            if not (pos_height["average"] == sf_pos):
                                                continue
                                            # 2 stir fry person is in colonial house
                                            if not (pos_food["stir fry"] == pos_style["colonial"]):
                                                continue
                                            # 8 beach = ranch
                                            if not (pos_vac["beach"] == pos_style["ranch"]):
                                                continue
                                            # 15 tall = beach
                                            if not (pos_height["tall"] == pos_vac["beach"]):
                                                continue
                                            # 16 tall left of Victorian (Victorian at 4)
                                            if not (pos_height["tall"] < 4):
                                                continue
                                            # 5 one house between average and Peter
                                            if abs(pos_height["average"] - pos_name["Peter"]) != 2:
                                                continue
                                            # 17 stir fry directly left of Bob
                                            if not (sf_pos + 1 == pos_name["Bob"]):
                                                continue
                                            # 18 modern left of Alice (index 4)
                                            if not (pos_style["modern"] < 4):
                                                continue
                                            # 19 craftsman left of short
                                            if not (pos_style["craftsman"] < pos_height["short"]):
                                                continue
                                            # 21 two houses between grilled cheese and super tall
                                            if abs(pos_food["grilled cheese"] - pos_height["super tall"]) != 3:
                                                continue
                                            # 24 cultural = pizza
                                            if not (pos_vac["cultural"] == pos_food["pizza"]):
                                                continue
                                            # 25 pizza left of cruise
                                            if not (pos_vac["cultural"] < pos_vac["cruise"]):
                                                continue
                                            # 6 craftsman not in house 3 (index 2)
                                            if pos_style["craftsman"] == 2:
                                                continue

                                            # Build solution rows
                                            result_rows = []
                                            for h in range(6):
                                                house_num = str(h+1)
                                                row = [
                                                    house_num,
                                                    name_at[h],
                                                    sa[h],
                                                    fa[h],
                                                    va[h],
                                                    ha[h],
                                                    ca1[h],
                                                ]
                                                result_rows.append(row)

                                            return {
                                                "solution": {
                                                    "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
                                                    "rows": result_rows
                                                }
                                            }
    return None

def main():
    solution = solve()
    if solution is None:
        print(json.dumps({"solution": {"header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"], "rows": []}}))
    else:
        print(json.dumps(solution, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()