import itertools as it
import json

def solve():
    houses = [1, 2, 3, 4, 5]

    # Attributes
    Names = ["Peter", "Arnold", "Eric", "Bob", "Alice"]
    Heights = ["average", "very tall", "very short", "short", "tall"]
    Cigars = ["prince", "dunhill", "blends", "pall mall", "blue master"]
    Smoothies = ["lime", "cherry", "dragonfruit", "watermelon", "desert"]
    Phones = ["oneplus 9", "samsung galaxy s21", "iphone 13", "huawei p50", "google pixel 6"]

    # Helpers
    def is_direct_left(a, b):
        return a + 1 == b

    def is_next_to(a, b):
        return abs(a - b) == 1

    # Iterate over permutations with progressive constraint pruning
    for name_perm in it.permutations(houses):
        pos_name = {Names[i]: name_perm[i] for i in range(5)}

        # Names-only constraints
        # 8. Bob is not in the fourth house.
        if pos_name["Bob"] == 4:
            continue
        # 2. There is one house between Eric and Alice. (distance 2)
        if abs(pos_name["Eric"] - pos_name["Alice"]) != 2:
            continue
        # 14. Two houses between very tall (Eric per 6) and Dragonfruit (Bob per 11) -> distance 3 between Eric and Bob
        if abs(pos_name["Eric"] - pos_name["Bob"]) != 3:
            continue
        # 9 implies Eric is not in the last house (must be directly left of Cherry)
        if pos_name["Eric"] == 5:
            continue

        for phone_perm in it.permutations(houses):
            pos_phone = {Phones[i]: phone_perm[i] for i in range(5)}

            # Phones constraints
            # 15. The person who uses an iPhone 13 is Eric.
            if pos_phone["iphone 13"] != pos_name["Eric"]:
                continue
            # 12. iPhone 13 and OnePlus 9 are next to each other.
            if not is_next_to(pos_phone["iphone 13"], pos_phone["oneplus 9"]):
                continue
            # 7. Arnold is directly left of the person who uses a Huawei P50.
            if not is_direct_left(pos_name["Arnold"], pos_phone["huawei p50"]):
                continue

            for smoothie_perm in it.permutations(houses):
                pos_smoothie = {Smoothies[i]: smoothie_perm[i] for i in range(5)}

                # Smoothies constraints
                # 11. Dragonfruit smoothie lover is Bob.
                if pos_smoothie["dragonfruit"] != pos_name["Bob"]:
                    continue
                # 9. Eric is directly left of the person who likes Cherry smoothies.
                if not is_direct_left(pos_name["Eric"], pos_smoothie["cherry"]):
                    continue
                # 16. Desert left of Lime.
                if not (pos_smoothie["desert"] < pos_smoothie["lime"]):
                    continue

                for cigar_perm in it.permutations(houses):
                    pos_cigar = {Cigars[i]: cigar_perm[i] for i in range(5)}

                    # Cigars constraints
                    # 10. Bob is the Dunhill smoker.
                    if pos_cigar["dunhill"] != pos_name["Bob"]:
                        continue
                    # 4. iPhone 13 is directly left of Blue Master.
                    if not is_direct_left(pos_phone["iphone 13"], pos_cigar["blue master"]):
                        continue
                    # 1. Prince smoker is the Desert smoothie lover.
                    if pos_cigar["prince"] != pos_smoothie["desert"]:
                        continue

                    for height_perm in it.permutations(houses):
                        pos_height = {Heights[i]: height_perm[i] for i in range(5)}

                        # Heights constraints
                        # 6. Eric is very tall.
                        if pos_height["very tall"] != pos_name["Eric"]:
                            continue
                        # 5. Average height is the Dunhill smoker.
                        if pos_height["average"] != pos_cigar["dunhill"]:
                            continue
                        # 3. Short is blends.
                        if pos_height["short"] != pos_cigar["blends"]:
                            continue
                        # 13. Samsung Galaxy S21 is the short person.
                        if pos_phone["samsung galaxy s21"] != pos_height["short"]:
                            continue
                        # 17. Arnold and the very short person are next to each other.
                        if not is_next_to(pos_name["Arnold"], pos_height["very short"]):
                            continue

                        # All constraints satisfied; build solution
                        # Invert mappings to get value by position
                        name_by_pos = {pos_name[n]: n for n in Names}
                        height_by_pos = {pos_height[h]: h for h in Heights}
                        cigar_by_pos = {pos_cigar[c]: c for c in Cigars}
                        smoothie_by_pos = {pos_smoothie[s]: s for s in Smoothies}
                        phone_by_pos = {pos_phone[p]: p for p in Phones}

                        rows = []
                        for h in houses:
                            rows.append([
                                str(h),
                                name_by_pos[h],
                                height_by_pos[h],
                                cigar_by_pos[h],
                                smoothie_by_pos[h],
                                phone_by_pos[h],
                            ])

                        result = {
                            "solution": {
                                "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
                                "rows": rows
                            }
                        }
                        return result

    raise ValueError("No solution found")

if __name__ == "__main__":
    solution = solve()
    print(json.dumps(solution))