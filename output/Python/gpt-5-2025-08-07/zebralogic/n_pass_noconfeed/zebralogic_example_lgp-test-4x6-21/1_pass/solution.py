import itertools
import json

def solve():
    houses = [1, 2, 3, 4]

    Names = ["Peter", "Arnold", "Alice", "Eric"]
    Flowers = ["roses", "daffodils", "carnations", "lilies"]
    Hobbies = ["photography", "painting", "cooking", "gardening"]
    Pets = ["dog", "fish", "bird", "cat"]
    Colors = ["red", "yellow", "green", "white"]
    Styles = ["craftsman", "colonial", "ranch", "victorian"]

    solutions = []

    # Helper to invert mapping attr->house to house->attr
    def invert(mapping):
        inv = {}
        for k, v in mapping.items():
            inv[v] = k
        return inv

    # Iterate over all possible assignments with pruning
    for name_perm in itertools.permutations(houses):
        name_pos = dict(zip(Names, name_perm))
        # Clue 6 and 1 together imply Arnold is in the Craftsman house (which is house 2)
        if name_pos["Arnold"] != 2:
            continue

        # Prepare style permutations, but enforce Craftsman at house 2 (Clue 6) and Eric in Victorian (Clue 7)
        # We'll iterate styles but prune early
        for style_perm in itertools.permutations(houses):
            style_pos = dict(zip(Styles, style_perm))
            if style_pos["craftsman"] != 2:
                continue
            if style_pos["victorian"] != name_pos["Eric"]:
                continue

            # Colors permutation; we'll enforce some constraints later
            for color_perm in itertools.permutations(houses):
                color_pos = dict(zip(Colors, color_perm))

                # Clue 13: colonial-style house is the person whose favorite color is red.
                if style_pos["colonial"] != color_pos["red"]:
                    continue

                # Flowers permutation; apply several constraints with colors and names
                for flower_perm in itertools.permutations(houses):
                    flower_pos = dict(zip(Flowers, flower_perm))

                    # Clue 5: roses <-> red
                    if flower_pos["roses"] != color_pos["red"]:
                        continue

                    # Clue 12: daffodils <-> yellow
                    if flower_pos["daffodils"] != color_pos["yellow"]:
                        continue

                    # Clue 10: white <-> carnations
                    if color_pos["white"] != flower_pos["carnations"]:
                        continue

                    # Clue 4: daffodils not in the fourth house
                    if flower_pos["daffodils"] == 4:
                        continue

                    # Clue 2: roses is to the right of Peter
                    if not (flower_pos["roses"] > name_pos["Peter"]):
                        continue

                    # Pets permutation
                    for pet_perm in itertools.permutations(houses):
                        pet_pos = dict(zip(Pets, pet_perm))

                        # Clue 8: fish <-> white
                        if pet_pos["fish"] != color_pos["white"]:
                            continue

                        # Clue 14: cat is Eric
                        if pet_pos["cat"] != name_pos["Eric"]:
                            continue

                        # Hobbies permutation
                        for hobby_perm in itertools.permutations(houses):
                            hobby_pos = dict(zip(Hobbies, hobby_perm))

                            # Clue 3: photography <-> dog
                            if hobby_pos["photography"] != pet_pos["dog"]:
                                continue

                            # Clue 9: cooking is to the right of red
                            if not (hobby_pos["cooking"] > color_pos["red"]):
                                continue

                            # Clue 11: white is to the right of gardening
                            if not (color_pos["white"] > hobby_pos["gardening"]):
                                continue

                            # Clue 1: Craftsman house is Arnold (already ensured Arnold at 2 and craftsman at 2)
                            # Clue 6: Craftsman is in second house (already enforced)
                            # All constraints satisfied

                            # Build solution rows
                            name_at = invert(name_pos)
                            flower_at = invert(flower_pos)
                            hobby_at = invert(hobby_pos)
                            pet_at = invert(pet_pos)
                            color_at = invert(color_pos)
                            style_at = invert(style_pos)

                            rows = []
                            for h in houses:
                                rows.append([
                                    str(h),
                                    name_at[h],
                                    flower_at[h],
                                    hobby_at[h],
                                    pet_at[h],
                                    color_at[h],
                                    style_at[h],
                                ])
                            solutions.append(rows)

    # Assuming unique solution; take the first
    if not solutions:
        raise RuntimeError("No solution found")

    rows = solutions[0]
    output = {
        "solution": {
            "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve()