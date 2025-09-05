import itertools
import json

def solve_puzzle():
    houses = (1, 2, 3, 4, 5)

    # Attributes
    names = ["Arnold", "Peter", "Eric", "Alice", "Bob"]
    hobbies = ["painting", "cooking", "knitting", "gardening", "photography"]
    heights = ["very tall", "tall", "very short", "average", "short"]
    foods = ["stew", "grilled cheese", "stir fry", "spaghetti", "pizza"]

    solutions = []

    # Iterate over all possible placements of names across houses
    for name_perm in itertools.permutations(houses):
        pos_name = dict(zip(names, name_perm))

        # Clue 3: Peter is not in the second house.
        if pos_name["Peter"] == 2:
            continue

        # Clue 8: Eric is not in the fifth house.
        if pos_name["Eric"] == 5:
            continue

        # Heights derived with constraints:
        # Clue 13: tall is in the third house.
        pos_height = {}
        pos_height["tall"] = 3

        # Clue 12: very short is in the fifth house.
        pos_height["very short"] = 5

        # Clue 9: short is Peter.
        pos_height["short"] = pos_name["Peter"]

        # Short cannot conflict with tall or very short
        if pos_height["short"] in (pos_height["tall"], pos_height["very short"]):
            continue

        # Choose average height position from remaining houses
        remaining_for_avg = [h for h in houses if h not in (pos_height["tall"], pos_height["very short"], pos_height["short"])]
        for avg_pos in remaining_for_avg:
            pos_height_local = dict(pos_height)
            pos_height_local["average"] = avg_pos
            # The remaining house is very tall
            pos_height_local["very tall"] = next(h for h in houses if h not in pos_height_local.values())

            # Foods
            pos_food = {}

            # Clue 2: grilled cheese is tall
            pos_food["grilled cheese"] = pos_height_local["tall"]  # 3

            # Clue 4: tall is directly left of stir fry
            pos_food["stir fry"] = pos_height_local["tall"] + 1  # must be 4
            if pos_food["stir fry"] not in houses:
                continue  # sanity

            # Clue 6: Alice is directly left of pizza
            pos_food["pizza"] = pos_name["Alice"] + 1
            if pos_food["pizza"] not in houses:
                continue

            # Ensure foods are unique so far
            if len({pos_food["grilled cheese"], pos_food["stir fry"], pos_food["pizza"]}) != 3:
                continue

            # Remaining foods: stew, spaghetti
            remaining_food_houses = [h for h in houses if h not in pos_food.values()]

            # Try both assignments for stew/spaghetti
            for spaghetti_pos, stew_pos in itertools.permutations(remaining_food_houses, 2):
                # Clue 7 (interpreted): The spaghetti eater is not in the second house.
                if spaghetti_pos == 2:
                    continue

                pos_food_local = dict(pos_food)
                pos_food_local["spaghetti"] = spaghetti_pos
                pos_food_local["stew"] = stew_pos

                # Hobbies
                pos_hobby = {}

                # Clue 11: painting is directly left of grilled cheese
                pos_hobby["painting"] = pos_food_local["grilled cheese"] - 1
                if pos_hobby["painting"] not in houses:
                    continue

                # Clue 5: cooking is average height
                pos_hobby["cooking"] = pos_height_local["average"]

                # Clue 1: Bob is the photography enthusiast
                pos_hobby["photography"] = pos_name["Bob"]

                # Check distinctness among current hobbies
                if len({pos_hobby["painting"], pos_hobby["cooking"], pos_hobby["photography"]}) != 3:
                    continue

                # Clue 10: average height and gardening are next to each other
                neighbors = []
                if pos_height_local["average"] - 1 in houses:
                    neighbors.append(pos_height_local["average"] - 1)
                if pos_height_local["average"] + 1 in houses:
                    neighbors.append(pos_height_local["average"] + 1)

                for gardening_pos in neighbors:
                    if gardening_pos in (pos_hobby["painting"], pos_hobby["cooking"], pos_hobby["photography"]):
                        continue
                    pos_hobby_local = dict(pos_hobby)
                    pos_hobby_local["gardening"] = gardening_pos

                    # Remaining hobby is knitting
                    used_hobby_houses = set(pos_hobby_local.values())
                    if len(used_hobby_houses) != 4:
                        continue
                    pos_hobby_local["knitting"] = next(h for h in houses if h not in used_hobby_houses)

                    # Clue 14: Alice is to the right of the photography enthusiast
                    if not (pos_name["Alice"] > pos_hobby_local["photography"]):
                        continue

                    # All constraints satisfied: build solution
                    solutions.append({
                        "names": pos_name.copy(),
                        "heights": pos_height_local.copy(),
                        "foods": pos_food_local.copy(),
                        "hobbies": pos_hobby_local.copy(),
                    })

    if not solutions:
        raise RuntimeError("No solution found.")

    # Assume unique solution; take the first
    sol = solutions[0]

    # Build per-house rows
    # Invert mappings for each category: house -> attribute
    house_to_name = {h: n for n, h in sol["names"].items()}
    house_to_height = {h: ht for ht, h in sol["heights"].items()}
    house_to_food = {h: f for f, h in sol["foods"].items()}
    house_to_hobby = {h: hb for hb, h in sol["hobbies"].items()}

    rows = []
    for h in sorted(houses):
        rows.append([
            str(h),
            house_to_name[h],
            house_to_hobby[h],
            house_to_height[h],
            house_to_food[h],
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Height", "Food"],
            "rows": rows
        }
    }
    return output


if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))