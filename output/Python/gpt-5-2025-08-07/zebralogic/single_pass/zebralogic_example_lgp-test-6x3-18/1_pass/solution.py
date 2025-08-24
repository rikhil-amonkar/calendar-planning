import json
from itertools import permutations

def solve_puzzle():
    houses = list(range(6))  # 0..5 represent houses 1..6
    names = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]
    mothers = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]
    pets = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]

    # Helper to check bounds
    def in_bounds(pos):
        return 0 <= pos < 6

    solution = None

    for pos_rabbit in houses:
        # Clue 4: hamster directly left of rabbit
        pos_hamster = pos_rabbit - 1
        if not in_bounds(pos_hamster):
            continue

        # Clue 2: two houses between cat and rabbit (distance 3)
        cat_candidates = []
        for c in [pos_rabbit - 3, pos_rabbit + 3]:
            if in_bounds(c):
                cat_candidates.append(c)
        for pos_cat in cat_candidates:
            # Clue 3: cat is directly left of Holly -> implies cat not in last house
            pos_holly = pos_cat + 1
            if not in_bounds(pos_holly):
                continue

            # Clue 6: one house between dog and cat (distance 2)
            dog_candidates = []
            for d in [pos_cat - 2, pos_cat + 2]:
                if in_bounds(d):
                    dog_candidates.append(d)
            for pos_dog in dog_candidates:
                # Ensure pet positions are unique
                pet_positions = {pos_rabbit, pos_hamster, pos_cat, pos_dog}
                if len(pet_positions) != 4:
                    continue

                # Assign remaining pets (bird and fish) to remaining two positions
                remaining_positions = [p for p in houses if p not in pet_positions]
                assert len(remaining_positions) == 2
                for pos_fish in remaining_positions:
                    pos_bird = remaining_positions[1] if remaining_positions[0] == pos_fish else remaining_positions[0]

                    # Build pet position map
                    pos_pet = {
                        "rabbit": pos_rabbit,
                        "hamster": pos_hamster,
                        "cat": pos_cat,
                        "dog": pos_dog,
                        "fish": pos_fish,
                        "bird": pos_bird,
                    }

                    # NAME assignments
                    # Clue 5: Rabbit is Eric
                    # Clue 10: Arnold has a cat
                    pos_name = {}
                    pos_name["Eric"] = pos_pet["rabbit"]
                    pos_name["Arnold"] = pos_pet["cat"]

                    # Clue 8: Alice is directly left of Carol
                    # Try all placements for Alice-Carol adjacency respecting current fixed names
                    for p in range(5):  # Alice at p, Carol at p+1
                        if p in pos_name.values() or (p + 1) in pos_name.values():
                            continue  # avoid colliding with Eric/Arnold
                        # Tentatively place Alice and Carol
                        pn = pos_name.copy()
                        pn["Alice"] = p
                        pn["Carol"] = p + 1

                        # Remaining names: Bob, Peter
                        remaining_name_positions = [h for h in houses if h not in pn.values()]
                        assert len(remaining_name_positions) == 2
                        # Clue 1: Bob is not in the second house (index 1)
                        for order in permutations(["Bob", "Peter"], 2):
                            pn2 = pn.copy()
                            pn2[order[0]] = remaining_name_positions[0]
                            pn2[order[1]] = remaining_name_positions[1]
                            if pn2["Bob"] == 1:
                                continue

                            # MOTHER assignments (deterministic given positions)
                            # Clue 7: Cat person has mother Janelle
                            # Clue 3: Cat directly left of Holly
                            # Clue 11: Rabbit person's mother is Kailyn
                            # Clue 9: Carol's mother is Aniya
                            # Clue 12: Fish person's mother is Sarah
                            pm = {}
                            pm["Janelle"] = pos_pet["cat"]
                            pm["Holly"] = pos_pet["cat"] + 1
                            pm["Kailyn"] = pos_pet["rabbit"]
                            pm["Aniya"] = pn2["Carol"]
                            pm["Sarah"] = pos_pet["fish"]

                            # Check for uniqueness so far
                            if len(set(pm.values())) != len(pm.values()):
                                continue

                            # Remaining mother is Penny
                            remaining_mother_pos = [h for h in houses if h not in pm.values()]
                            if len(remaining_mother_pos) != 1:
                                continue
                            pm["Penny"] = remaining_mother_pos[0]

                            # Final validation of all clues (redundant but safe)
                            def check_all():
                                # Clue 1
                                if pn2["Bob"] == 1:
                                    return False
                                # Clue 2
                                if abs(pos_pet["cat"] - pos_pet["rabbit"]) != 3:
                                    return False
                                # Clue 3
                                if pos_pet["cat"] + 1 != pm["Holly"]:
                                    return False
                                # Clue 4
                                if pos_pet["hamster"] + 1 != pos_pet["rabbit"]:
                                    return False
                                # Clue 5
                                if pn2["Eric"] != pos_pet["rabbit"]:
                                    return False
                                # Clue 6
                                if abs(pos_pet["dog"] - pos_pet["cat"]) != 2:
                                    return False
                                # Clue 7
                                if pos_pet["cat"] != pm["Janelle"]:
                                    return False
                                # Clue 8
                                if pn2["Alice"] + 1 != pn2["Carol"]:
                                    return False
                                # Clue 9
                                if pn2["Carol"] != pm["Aniya"]:
                                    return False
                                # Clue 10
                                if pn2["Arnold"] != pos_pet["cat"]:
                                    return False
                                # Clue 11
                                if pm["Kailyn"] != pos_pet["rabbit"]:
                                    return False
                                # Clue 12
                                if pos_pet["fish"] != pm["Sarah"]:
                                    return False
                                return True

                            if not check_all():
                                continue

                            # Build solution mapping per house
                            name_by_pos = {v: k for k, v in pn2.items()}
                            mother_by_pos = {v: k for k, v in pm.items()}
                            pet_by_pos = {v: k for k, v in pos_pet.items()}

                            rows = []
                            for i in range(6):
                                house_number = str(i + 1)
                                rows.append([house_number, name_by_pos[i], mother_by_pos[i], pet_by_pos[i]])

                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Mother", "Pet"],
                                    "rows": rows
                                }
                            }
                            return solution
    return None

def main():
    result = solve_puzzle()
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()