import json
import itertools

def solve():
    houses = [1, 2, 3, 4, 5]

    names = ["Bob", "Arnold", "Alice", "Peter", "Eric"]
    hobbies = ["cooking", "gardening", "painting", "photography", "knitting"]
    sports = ["swimming", "tennis", "soccer", "baseball", "basketball"]
    styles = ["ranch", "craftsman", "victorian", "modern", "colonial"]
    children = ["Timothy", "Samantha", "Bella", "Meredith", "Fred"]
    heights = ["average", "very tall", "very short", "short", "tall"]

    def is_next_to(a, b):
        return abs(a - b) == 1

    # Pre-assign fixed constraints
    # Alice is tall and in house 2
    # Peter is very tall and in house 4
    # Victorian is in house 5
    # Gardening is in house 2
    # Tall is in house 2
    # Very tall is in house 4
    # Peter directly left of Victorian (thus Peter 4, Victorian 5 already satisfies)
    # These will be enforced in the loops

    for bob_house, arnold_house, eric_house in itertools.permutations([1, 3, 5], 3):
        # Names positions
        name_pos = {
            "Alice": 2,
            "Peter": 4,
            "Bob": bob_house,
            "Arnold": arnold_house,
            "Eric": eric_house
        }

        # Styles: fix Victorian=5; assign others to 1..4
        style_values = ["ranch", "craftsman", "modern", "colonial"]
        for perm in itertools.permutations([1, 2, 3, 4], 4):
            style_pos = {
                "victorian": 5,
                style_values[0]: perm[0],
                style_values[1]: perm[1],
                style_values[2]: perm[2],
                style_values[3]: perm[3],
            }

            # Constraints on styles:
            # Craftsman cannot be 2 (since 2 is tall, but craftsman=average) or 4 (4 is very tall)
            if style_pos["craftsman"] in (2, 4):
                continue
            # Modern cannot be 2 because modern=cooking and 2 has gardening
            if style_pos["modern"] == 2:
                continue
            # Peter directly left of Victorian already satisfied by Peter=4 and Victorian=5
            # Ranch is somewhere to the left of cooking (which is at modern)
            if not (style_pos["ranch"] < style_pos["modern"]):
                continue

            # Heights
            height_pos = {}
            height_pos["tall"] = 2
            height_pos["very tall"] = 4
            # Average equals Craftsman
            height_pos["average"] = style_pos["craftsman"]
            # Remaining heights: "very short" and "short" to remaining two houses
            remaining_houses_for_heights = [h for h in houses if h not in {height_pos["tall"], height_pos["very tall"], height_pos["average"]}]
            for vs_house, short_house in itertools.permutations(remaining_houses_for_heights, 2):
                height_pos["very short"] = vs_house
                height_pos["short"] = short_house

                # Constraint: very short is to the right of Eric
                if not (height_pos["very short"] > name_pos["Eric"]):
                    continue

                # Hobbies
                hobby_pos = {}
                hobby_pos["gardening"] = 2
                # Modern = cooking
                hobby_pos["cooking"] = style_pos["modern"]
                # Bob = painting
                hobby_pos["painting"] = name_pos["Bob"]

                # Ensure hobby uniqueness so far
                used_hobby_houses = {hobby_pos["gardening"], hobby_pos["cooking"], hobby_pos["painting"]}
                if len(used_hobby_houses) != 3:
                    continue  # conflict (shouldn't happen, but safe)

                # Knitting next to gardening (house 2), so house 1 or 3, and not already taken
                possible_knitting_houses = [h for h in [1, 3] if h not in used_hobby_houses]
                if not possible_knitting_houses:
                    continue
                for knit_house in possible_knitting_houses:
                    hobby_pos_local = dict(hobby_pos)
                    hobby_pos_local["knitting"] = knit_house
                    # Remaining hobby is photography to the last free house
                    remaining_houses_for_hobby = [h for h in houses if h not in set(hobby_pos_local.values())]
                    if len(remaining_houses_for_hobby) != 1:
                        continue
                    hobby_pos_local["photography"] = remaining_houses_for_hobby[0]

                    # Sports
                    sport_pos = {}
                    # Baseball = very tall
                    sport_pos["baseball"] = height_pos["very tall"]  # should be 4
                    if sport_pos["baseball"] != 4:
                        continue
                    # Tennis = modern
                    sport_pos["tennis"] = style_pos["modern"]
                    # Basketball = short
                    sport_pos["basketball"] = height_pos["short"]
                    # Remaining sports: soccer and swimming to remaining houses
                    used_sport_houses = {sport_pos["baseball"], sport_pos["tennis"], sport_pos["basketball"]}
                    remaining_houses_for_sports = [h for h in houses if h not in used_sport_houses]
                    for soccer_house, swimming_house in itertools.permutations(remaining_houses_for_sports, 2):
                        # Soccer not in first house
                        if soccer_house == 1:
                            continue
                        sport_pos_local = dict(sport_pos)
                        sport_pos_local["soccer"] = soccer_house
                        sport_pos_local["swimming"] = swimming_house

                        # Children
                        child_pos = {}
                        # Fred = Victorian = 5
                        child_pos["Fred"] = style_pos["victorian"] if "victorian" in style_pos else 5
                        # Samantha = modern
                        child_pos["Samantha"] = style_pos["modern"]
                        # Meredith = average = craftsman
                        child_pos["Meredith"] = height_pos["average"]
                        # Timothy next to Meredith
                        timothy_candidates = [h for h in houses if is_next_to(h, child_pos["Meredith"]) and h not in {child_pos["Fred"], child_pos["Samantha"], child_pos["Meredith"]}]
                        if not timothy_candidates:
                            continue
                        for tim_house in timothy_candidates:
                            child_pos_local = dict(child_pos)
                            child_pos_local["Timothy"] = tim_house
                            # Remaining child is Bella to the last free house
                            remaining_house_for_bella = [h for h in houses if h not in set(child_pos_local.values())]
                            if len(remaining_house_for_bella) != 1:
                                continue
                            child_pos_local["Bella"] = remaining_house_for_bella[0]

                            # Final consistency checks across all:
                            # Alice is tall and in second house - already ensured by name_pos and height_pos
                            if not (name_pos["Alice"] == 2 and height_pos["tall"] == 2):
                                continue
                            # Bob paints - ensured by hobby_pos_local['painting'] == name_pos['Bob']
                            if hobby_pos_local["painting"] != name_pos["Bob"]:
                                continue
                            # Knitting next to gardening - ensured
                            if not is_next_to(hobby_pos_local["knitting"], hobby_pos_local["gardening"]):
                                continue
                            # Modern=cooking and Tennis=Samantha=Modern - ensured by construction

                            # Build the solution table per house
                            house_info = {}
                            for h in houses:
                                # Find values for each category at house h
                                name_at_h = next(n for n, pos in name_pos.items() if pos == h)
                                hobby_at_h = next(hb for hb, pos in hobby_pos_local.items() if pos == h)
                                sport_at_h = next(sp for sp, pos in sport_pos_local.items() if pos == h)
                                style_at_h = next(st for st, pos in style_pos.items() if pos == h)
                                child_at_h = next(ch for ch, pos in child_pos_local.items() if pos == h)
                                height_at_h = next(ht for ht, pos in height_pos.items() if pos == h)
                                house_info[h] = {
                                    "name": name_at_h,
                                    "hobby": hobby_at_h,
                                    "favorite sports": sport_at_h,
                                    "style of house": style_at_h,
                                    "child": child_at_h,
                                    "heights": height_at_h
                                }

                            # Return the first valid complete solution
                            return house_info

    return None

solution = solve()

output = {
    "solution": {
        "header": ["House", "name", "hobby", "favorite sports", "style of house", "child", "heights"],
        "rows": []
    }
}

if solution:
    for h in [1, 2, 3, 4, 5]:
        row = [
            str(h),
            solution[h]["name"],
            solution[h]["hobby"],
            solution[h]["favorite sports"],
            solution[h]["style of house"],
            solution[h]["child"],
            solution[h]["heights"]
        ]
        output["solution"]["rows"].append(row)

print(json.dumps(output, indent=2))