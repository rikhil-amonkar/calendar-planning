import json
import itertools

def solve():
    houses = list(range(5))  # positions 0..4 correspond to houses 1..5

    Names = ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice']
    Heights = ['average', 'very tall', 'very short', 'short', 'tall']
    Cigars = ['prince', 'dunhill', 'blends', 'pall mall', 'blue master']
    Smoothies = ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert']
    Phones = ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6']

    # Helper to invert mapping value->position into position->value list
    def invert(pos_map, values):
        result = [None]*5
        for v in values:
            result[pos_map[v]] = v
        return result

    # Search over permutations with incremental constraints
    for name_perm in itertools.permutations(Names):
        pos_name = {name_perm[i]: i for i in range(5)}

        # Name-only constraints:
        # 2. One house between Eric and Alice
        if abs(pos_name['Eric'] - pos_name['Alice']) != 2:
            continue
        # 8. Bob is not in the fourth house (index 3)
        if pos_name['Bob'] == 3:
            continue
        # 9. Eric is directly left of Cherry (implies Eric not at last position)
        if pos_name['Eric'] == 4:
            continue
        # 6, 11, 14 -> Eric very tall and Dragonfruit is Bob, with two houses between (distance 3)
        if abs(pos_name['Eric'] - pos_name['Bob']) != 3:
            continue

        # Smoothies:
        # Pre-assign bob->dragonfruit and eric->left of cherry
        s_pos = {}
        s_pos['dragonfruit'] = pos_name['Bob']
        s_pos['cherry'] = pos_name['Eric'] + 1  # 9, 15: Eric left of Cherry by 1

        # Build remaining smoothies assignments
        remaining_smoothies = [s for s in Smoothies if s not in s_pos]
        used_positions = {s_pos['dragonfruit'], s_pos['cherry']}
        remaining_positions = [p for p in houses if p not in used_positions]

        for perm_pos in itertools.permutations(remaining_positions):
            tmp_s_pos = dict(s_pos)
            for s, p in zip(remaining_smoothies, perm_pos):
                tmp_s_pos[s] = p

            # 16. Desert left of Lime
            if not (tmp_s_pos['desert'] < tmp_s_pos['lime']):
                continue

            # Cigars:
            c_pos = {}
            # 10. Bob is the Dunhill smoker.
            c_pos['dunhill'] = pos_name['Bob']
            # 4, 9, 15 together imply Blue Master is in the Cherry house
            c_pos['blue master'] = tmp_s_pos['cherry']
            # 1. Prince smoker is the Desert smoothie lover.
            c_pos['prince'] = tmp_s_pos['desert']

            # Ensure these three are all distinct houses
            if len({c_pos['dunhill'], c_pos['blue master'], c_pos['prince']}) != 3:
                continue

            remaining_cigars = [c for c in Cigars if c not in c_pos]
            remaining_positions_c = [p for p in houses if p not in set(c_pos.values())]

            for perm_c in itertools.permutations(remaining_positions_c):
                tmp_c_pos = dict(c_pos)
                for c, p in zip(remaining_cigars, perm_c):
                    tmp_c_pos[c] = p

                # Heights:
                h_pos = {}
                # 6. Eric is the person who is very tall.
                h_pos['very tall'] = pos_name['Eric']
                # 5. Average is Dunhill smoker -> and 10: Bob is Dunhill -> Bob is average.
                h_pos['average'] = tmp_c_pos['dunhill']
                if h_pos['average'] != pos_name['Bob']:
                    continue
                # 3. Short is Blends smoker.
                h_pos['short'] = tmp_c_pos['blends']
                # 14. Two houses between very tall and dragonfruit lover.
                if abs(h_pos['very tall'] - tmp_s_pos['dragonfruit']) != 3:
                    continue

                # Remaining heights: 'very short' and 'tall' occupy the remaining positions
                assigned_height_positions = {h_pos['very tall'], h_pos['average'], h_pos['short']}
                rem_positions_h = [p for p in houses if p not in assigned_height_positions]

                # 17. Arnold and the person who is very short are next to each other.
                placed = False
                for very_short_pos in rem_positions_h:
                    if abs(pos_name['Arnold'] - very_short_pos) != 1:
                        continue
                    tmp_h_pos = dict(h_pos)
                    tmp_h_pos['very short'] = very_short_pos
                    # The other remaining position is 'tall'
                    other_pos = [p for p in rem_positions_h if p != very_short_pos][0]
                    tmp_h_pos['tall'] = other_pos

                    # Phones:
                    p_pos = {}
                    # 15. iPhone 13 is Eric.
                    p_pos['iphone 13'] = pos_name['Eric']
                    # 13. Samsung Galaxy S21 is the person who is short.
                    p_pos['samsung galaxy s21'] = tmp_h_pos['short']
                    # 7. Arnold is directly left of the person who uses a Huawei P50.
                    huawei_pos = pos_name['Arnold'] + 1
                    if not (0 <= huawei_pos <= 4):
                        continue
                    p_pos['huawei p50'] = huawei_pos

                    # Check distinct so far
                    if len(set(p_pos.values())) != len(p_pos):
                        continue

                    # Remaining phones: oneplus 9 and google pixel 6
                    remaining_phones = [ph for ph in Phones if ph not in p_pos]
                    remaining_positions_p = [p for p in houses if p not in set(p_pos.values())]

                    # 12. iPhone 13 and OnePlus 9 are next to each other.
                    iphone_pos = p_pos['iphone 13']
                    neighbors = set()
                    if iphone_pos - 1 >= 0:
                        neighbors.add(iphone_pos - 1)
                    if iphone_pos + 1 <= 4:
                        neighbors.add(iphone_pos + 1)

                    # 4. iPhone 13 directly left of Blue Master.
                    if not (iphone_pos + 1 == tmp_c_pos['blue master']):
                        continue

                    # Assign remaining phones with the adjacency constraint for OnePlus 9
                    success_phone = False
                    for perm_p in itertools.permutations(remaining_positions_p):
                        tmp_p_pos = dict(p_pos)
                        for ph, pp in zip(remaining_phones, perm_p):
                            tmp_p_pos[ph] = pp
                        # Check adjacency for OnePlus 9
                        if tmp_p_pos['oneplus 9'] not in neighbors:
                            continue
                        # All constraints satisfied; record solution
                        pos_name_final = pos_name
                        pos_height_final = tmp_h_pos
                        pos_cigar_final = tmp_c_pos
                        pos_smoothie_final = tmp_s_pos
                        pos_phone_final = tmp_p_pos
                        placed = True
                        success_phone = True
                        break
                    if placed and success_phone:
                        break
                if placed:
                    # Build output rows
                    names_by_pos = invert(pos_name_final, Names)
                    heights_by_pos = invert(pos_height_final, Heights)
                    cigars_by_pos = invert(pos_cigar_final, Cigars)
                    smoothies_by_pos = invert(pos_smoothie_final, Smoothies)
                    phones_by_pos = invert(pos_phone_final, Phones)

                    rows = []
                    for i in range(5):
                        rows.append([
                            str(i+1),
                            names_by_pos[i],
                            heights_by_pos[i],
                            cigars_by_pos[i],
                            smoothies_by_pos[i],
                            phones_by_pos[i],
                        ])

                    result = {
                        "solution": {
                            "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
                            "rows": rows
                        }
                    }
                    return result
    return None

if __name__ == "__main__":
    solution = solve()
    print(json.dumps(solution, ensure_ascii=False, indent=2))