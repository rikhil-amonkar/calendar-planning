import json
from itertools import permutations

def solve_puzzle():
    # Houses are indexed 0..4 representing 1..5 from left to right
    houses = list(range(5))

    # Attributes
    names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    smoothies = ["lime", "dragonfruit", "desert", "watermelon", "cherry"]
    animals = ["horse", "dog", "bird", "fish", "cat"]
    nationalities = ["german", "swede", "norwegian", "brit", "dane"]

    # Helper to invert a mapping name->index to index->name
    def invert(pos_map):
        return {idx: key for key, idx in pos_map.items()}

    solution = None

    # Generate animal positions with horse fixed at house 3 (index 2)
    animal_positions_remaining = [i for i in houses if i != 2]
    for perm_anim in permutations(animal_positions_remaining, 4):
        pos_animal = {
            "horse": 2,
            "dog": perm_anim[0],
            "bird": perm_anim[1],
            "fish": perm_anim[2],
            "cat": perm_anim[3],
        }

        # Clue 4: bird right of cat
        if not (pos_animal["bird"] > pos_animal["cat"]):
            continue

        dog_idx = pos_animal["dog"]

        # Clue 5: dog is directly left of lime -> dog can't be at last house
        if dog_idx == 4:
            continue

        # Clue 1: Swede directly left of dog -> swede_idx = dog_idx - 1 must be valid
        swede_idx = dog_idx - 1
        if swede_idx < 0:
            continue

        # Nationalities: dane is horse (Clue 3 and 11 -> dane at index 2)
        # Clue 2: There are two houses between dog owner and Brit -> |dog - brit| = 3
        possible_brit_positions = []
        if dog_idx - 3 >= 0:
            possible_brit_positions.append(dog_idx - 3)
        if dog_idx + 3 <= 4:
            possible_brit_positions.append(dog_idx + 3)

        for brit_idx in possible_brit_positions:
            # Build nationality positions ensuring uniqueness
            used_nat_positions = {2, swede_idx, brit_idx}
            if len(used_nat_positions) != 3:
                # Overlap invalid (e.g., brit overlaps dane or swede)
                continue

            remaining_nat_positions = [i for i in houses if i not in used_nat_positions]
            # Remaining nationalities are german and norwegian
            for perm_nat_rest in permutations(remaining_nat_positions, 2):
                pos_nat = {
                    "dane": 2,
                    "swede": swede_idx,
                    "brit": brit_idx,
                    "german": perm_nat_rest[0],
                    "norwegian": perm_nat_rest[1],
                }

                # Smoothies:
                # Clue 5: dog left of lime -> lime at dog_idx + 1
                # Clue 10: desert = dog
                # Clue 9: bird = watermelon
                pos_smoothie = {
                    "lime": dog_idx + 1,
                    "desert": dog_idx,
                    "watermelon": pos_animal["bird"],
                }
                # Ensure uniqueness among fixed smoothies
                if len(set(pos_smoothie.values())) != 3:
                    continue

                remaining_smoothie_positions = [i for i in houses if i not in pos_smoothie.values()]
                # Remaining smoothies: dragonfruit, cherry
                for cherry_pos, dragon_pos in [(remaining_smoothie_positions[0], remaining_smoothie_positions[1]),
                                               (remaining_smoothie_positions[1], remaining_smoothie_positions[0])]:
                    pos_s = dict(pos_smoothie)
                    pos_s["cherry"] = cherry_pos
                    pos_s["dragonfruit"] = dragon_pos

                    # Names:
                    # Clue 6: Eric is the cat lover
                    # Clue 7: Bob is the bird keeper
                    # Clue 12: The Norwegian is Alice
                    pos_name = {
                        "Eric": pos_animal["cat"],
                        "Bob": pos_animal["bird"],
                        "Alice": pos_nat["norwegian"],
                    }
                    # Ensure distinct so far
                    if len(set(pos_name.values())) < 3:
                        continue

                    # Clue 8: Cherry is directly left of Peter
                    cherry_idx = pos_s["cherry"]
                    peter_idx = cherry_idx + 1
                    if peter_idx > 4:
                        continue
                    # Peter's position must be free among already assigned names
                    if peter_idx in pos_name.values():
                        # If already occupied by a different fixed name, invalid
                        continue
                    pos_name["Peter"] = peter_idx

                    # Assign the remaining name to the remaining house
                    used_name_positions = set(pos_name.values())
                    remaining_positions = [i for i in houses if i not in used_name_positions]
                    if len(remaining_positions) != 1:
                        continue
                    pos_name["Arnold"] = remaining_positions[0]

                    # Final validation of all clues to be safe
                    # 1
                    if not (pos_nat["swede"] + 1 == pos_animal["dog"]):
                        continue
                    # 2
                    if not (abs(pos_animal["dog"] - pos_nat["brit"]) == 3):
                        continue
                    # 3
                    if not (pos_nat["dane"] == pos_animal["horse"] == 2):
                        continue
                    # 4
                    if not (pos_animal["bird"] > pos_animal["cat"]):
                        continue
                    # 5
                    if not (pos_animal["dog"] + 1 == pos_s["lime"]):
                        continue
                    # 6
                    if not (pos_name["Eric"] == pos_animal["cat"]):
                        continue
                    # 7
                    if not (pos_name["Bob"] == pos_animal["bird"]):
                        continue
                    # 8
                    if not (pos_s["cherry"] + 1 == pos_name["Peter"]):
                        continue
                    # 9
                    if not (pos_s["watermelon"] == pos_animal["bird"]):
                        continue
                    # 10
                    if not (pos_s["desert"] == pos_animal["dog"]):
                        continue
                    # 11
                    if not (pos_animal["horse"] == 2):
                        continue
                    # 12
                    if not (pos_name["Alice"] == pos_nat["norwegian"]):
                        continue

                    # Build final rows
                    inv_name = invert(pos_name)
                    inv_smoothie = invert(pos_s)
                    inv_animal = invert(pos_animal)
                    inv_nat = invert(pos_nat)

                    rows = []
                    for i in houses:
                        rows.append([
                            str(i + 1),
                            inv_name[i],
                            inv_smoothie[i],
                            inv_animal[i],
                            inv_nat[i],
                        ])

                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
                            "rows": rows
                        }
                    }
                    return solution

    return None

if __name__ == "__main__":
    result = solve_puzzle()
    if result is None:
        print(json.dumps({"solution": {"header": ["House", "Name", "Smoothie", "Animal", "Nationality"], "rows": []}}))
    else:
        print(json.dumps(result, ensure_ascii=False))