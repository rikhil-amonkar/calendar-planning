import json
import itertools

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
    children = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
    smoothies = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]

    # Helper to invert list of values per house into mapping value -> position (1-indexed)
    def invert_mapping(house_values):
        return {val: idx+1 for idx, val in enumerate(house_values)}

    solutions = []

    # Iterate over all permutations of children placements
    for child_perm in itertools.permutations(children):
        pos_child = invert_mapping(child_perm)

        # Clue 13: Meredith is in the sixth house.
        if child_perm[5] != "Meredith":
            continue

        # Clue 4: Samantha is not in the second house.
        if pos_child["Samantha"] == 2:
            continue

        # Derived from Clue 12: Cherry directly left of Samantha => Samantha cannot be at house 1
        if pos_child["Samantha"] == 1:
            continue

        # Clue 3 + 6: Alice (name) not in 5 and Alice is the mother of child Alice => child Alice not in 5
        if pos_child["Alice"] == 5:
            continue

        # Smoothies assignment with constraints
        # Set fixed smoothie positions from clues
        # Clue 14: Dragonfruit smoothie lover is the mother's child named Meredith -> same house
        pos_dragonfruit = pos_child["Meredith"]
        # Clue 12: Cherry is directly left of Samantha
        cherry_pos = pos_child["Samantha"] - 1
        if not (1 <= cherry_pos <= 6):
            continue

        # Clue 6 and 7: Alice is mother of Alice (child) and drinks Watermelon
        # => Watermelon is at the house where child is Alice
        pos_watermelon = pos_child["Alice"]

        # Clue 5: Watermelon is somewhere to the right of Cherry
        if not (pos_watermelon > cherry_pos):
            continue

        # Now assign the rest of smoothies with constraints:
        # - Clue 1: Fred's house is next to the Desert smoothie
        # - Clue 2: Blueberry is somewhere to the left of Fred
        fpos = pos_child["Fred"]

        # initialize used positions
        used = set([pos_dragonfruit, cherry_pos, pos_watermelon])
        if len(used) != 3:
            # if any of these overlap, invalid
            continue

        # Determine possible positions for 'desert' adjacent to Fred
        desert_candidates = []
        for dpos in [fpos - 1, fpos + 1]:
            if 1 <= dpos <= 6 and dpos not in used:
                desert_candidates.append(dpos)

        for dpos in desert_candidates:
            used2 = set(used)
            used2.add(dpos)

            # Blueberry must be left of Fred and unassigned
            blueberry_candidates = [p for p in houses if p not in used2 and p < fpos]
            for bpos in blueberry_candidates:
                used3 = set(used2)
                used3.add(bpos)

                # Remaining smoothie 'lime' goes to the last remaining house
                remaining_positions = [p for p in houses if p not in used3]
                if len(remaining_positions) != 1:
                    continue
                lpos = remaining_positions[0]

                # Build smoothie positions mapping
                pos_smoothie = {
                    "dragonfruit": pos_dragonfruit,
                    "cherry": cherry_pos,
                    "watermelon": pos_watermelon,
                    "desert": dpos,
                    "blueberry": bpos,
                    "lime": lpos
                }

                # Names assignment with constraints
                # Known:
                # - Clue 6: Alice (name) is the mother of child Alice
                # - Clue 7: Alice drinks Watermelon -> consistent with pos_watermelon
                pos_name_alice = pos_child["Alice"]
                # Clue 3 already ensured Alice not in 5 via child position check

                # Clue 10: Bob is the mother of Timothy
                pos_name_bob = pos_child["Timothy"]

                # Occupied by Alice and Bob
                occupied = {pos_name_alice, pos_name_bob}
                if len(occupied) != 2:
                    # If they overlap (shouldn't), invalid
                    continue

                available_positions = [p for p in houses if p not in occupied]

                # Place Arnold and Carol (Clue 11: Arnold directly left of Carol)
                # Clue 9: Arnold is not in the second house.
                sam_pos = pos_child["Samantha"]
                found = False

                for a_pos in available_positions:
                    if a_pos == 6:  # cannot be left of anyone
                        continue
                    if a_pos == 2:  # Arnold not in second house
                        continue
                    c_pos = a_pos + 1
                    if c_pos not in available_positions:
                        continue

                    # Now remaining positions for Peter and Eric
                    rem_after_ac = [p for p in available_positions if p not in {a_pos, c_pos}]
                    if len(rem_after_ac) != 2:
                        continue

                    # Clue 8: Peter is somewhere to the right of Samantha
                    peter_candidates = [p for p in rem_after_ac if p > sam_pos]
                    for p_pos in peter_candidates:
                        e_pos = rem_after_ac[0] if rem_after_ac[1] == p_pos else rem_after_ac[1]

                        # Build name positions
                        pos_name = {
                            "Alice": pos_name_alice,
                            "Bob": pos_name_bob,
                            "Arnold": a_pos,
                            "Carol": c_pos,
                            "Peter": p_pos,
                            "Eric": e_pos
                        }

                        # Final consistency checks (redundant but safe)
                        if pos_name["Alice"] != pos_child["Alice"]:
                            continue
                        if pos_smoothie["watermelon"] != pos_name["Alice"]:
                            continue
                        if pos_name["Peter"] <= sam_pos:
                            continue

                        # Construct final per-house rows
                        house_to_name = {v: k for k, v in pos_name.items()}
                        house_to_child = {v: k for k, v in pos_child.items()}
                        house_to_smoothie = {v: k for k, v in pos_smoothie.items()}

                        rows = []
                        for h in houses:
                            rows.append([
                                str(h),
                                house_to_name[h],
                                house_to_child[h],
                                house_to_smoothie[h]
                            ])

                        solutions.append({
                            "solution": {
                                "header": ["House", "Name", "Children", "Smoothie"],
                                "rows": rows
                            }
                        })
                        found = True
                        break
                    if found:
                        break
                if found:
                    break
            if solutions:
                break
        if solutions:
            break

    # If no solution found (shouldn't happen), raise an error
    if not solutions:
        raise RuntimeError("No solution found for the puzzle.")

    # Output the first (should be unique) solution as JSON
    return solutions[0]

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))