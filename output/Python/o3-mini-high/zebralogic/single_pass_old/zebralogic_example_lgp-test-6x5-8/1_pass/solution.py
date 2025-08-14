#!/usr/bin/env python3
import json
from itertools import product
import sys

def check_constraints(houses, num_assigned):
    # C1. The person who is an engineer is the dog owner.
    for i in range(num_assigned):
        occ = houses[i]["Occupation"]
        animal = houses[i]["Animal"]
        if occ is not None:
            if occ == "engineer" and animal is not None and animal != "dog":
                return False
        if animal is not None:
            if animal == "dog" and occ is not None and occ != "engineer":
                return False

    # C2. The person who has an average height is somewhere to the left of the person who is short.
    idx_average = None
    idx_short = None
    for i in range(num_assigned):
        h = houses[i]["Height"]
        if h == "average":
            idx_average = i
        if h == "short":
            idx_short = i
    if idx_average is not None and idx_short is not None:
        if idx_average >= idx_short:
            return False

    # C3. The person who has an average height is directly left of the rabbit owner.
    for i in range(num_assigned - 1):
        h1 = houses[i]["Height"]
        a2 = houses[i+1]["Animal"]
        if h1 == "average":
            if a2 is not None and a2 != "rabbit":
                return False
        if a2 == "rabbit":
            if h1 is not None and h1 != "average":
                return False

    # C4. The person who is tall is somewhere to the left of the person who is very short.
    idx_tall = None
    idx_vshort = None
    for i in range(num_assigned):
        h = houses[i]["Height"]
        if h == "tall":
            idx_tall = i
        if h == "very short":
            idx_vshort = i
    if idx_tall is not None and idx_vshort is not None:
        if idx_tall >= idx_vshort:
            return False

    # C5. Arnold is the cat lover.
    for i in range(num_assigned):
        name = houses[i]["Name"]
        animal = houses[i]["Animal"]
        if name == "Arnold":
            if animal is not None and animal != "cat":
                return False
        if animal == "cat":
            if name is not None and name != "Arnold":
                return False

    # C6. The person who keeps horses is the person who is a teacher.
    for i in range(num_assigned):
        occ = houses[i]["Occupation"]
        animal = houses[i]["Animal"]
        if animal == "horse":
            if occ is not None and occ != "teacher":
                return False
        if occ == "teacher":
            if animal is not None and animal != "horse":
                return False

    # C7. Carol is the person who loves soccer.
    for i in range(num_assigned):
        name = houses[i]["Name"]
        sport = houses[i]["Favorite Sport"]
        if name == "Carol":
            if sport is not None and sport != "soccer":
                return False
        if sport == "soccer":
            if name is not None and name != "Carol":
                return False

    # C8. The person who is tall is the person who loves volleyball.
    for i in range(num_assigned):
        height = houses[i]["Height"]
        sport = houses[i]["Favorite Sport"]
        if height == "tall":
            if sport is not None and sport != "volleyball":
                return False
        if sport == "volleyball":
            if height is not None and height != "tall":
                return False

    # C9. The person who is a lawyer is in the fifth house.
    if num_assigned > 4:
        if houses[4]["Occupation"] is not None and houses[4]["Occupation"] != "lawyer":
            return False

    # C10. The person who loves tennis is the person who is a teacher.
    for i in range(num_assigned):
        sport = houses[i]["Favorite Sport"]
        occ = houses[i]["Occupation"]
        if sport == "tennis":
            if occ is not None and occ != "teacher":
                return False
        if occ == "teacher":
            if sport is not None and sport != "tennis":
                return False

    # C11. The person who has an average height is the person who loves swimming.
    for i in range(num_assigned):
        height = houses[i]["Height"]
        sport = houses[i]["Favorite Sport"]
        if height == "average":
            if sport is not None and sport != "swimming":
                return False
        if sport == "swimming":
            if height is not None and height != "average":
                return False

    # C12. The person who loves baseball is directly left of the person who is an engineer.
    for i in range(num_assigned - 1):
        sport = houses[i]["Favorite Sport"]
        occ_next = houses[i+1]["Occupation"]
        if sport == "baseball":
            if occ_next is not None and occ_next != "engineer":
                return False
        if occ_next == "engineer":
            if sport is not None and sport != "baseball":
                return False

    # C13. Peter is the person who is a nurse.
    for i in range(num_assigned):
        name = houses[i]["Name"]
        occ = houses[i]["Occupation"]
        if name == "Peter":
            if occ is not None and occ != "nurse":
                return False
        if occ == "nurse":
            if name is not None and name != "Peter":
                return False

    # C14. Bob is somewhere to the right of the person who is an artist.
    artist_index = None
    bob_index = None
    for i in range(num_assigned):
        if houses[i]["Occupation"] == "artist":
            artist_index = i
        if houses[i]["Name"] == "Bob":
            bob_index = i
    if artist_index is not None and bob_index is not None:
        if bob_index <= artist_index:
            return False

    # C15. The person who is a teacher is directly left of the person who loves soccer.
    for i in range(num_assigned - 1):
        occ = houses[i]["Occupation"]
        sport_next = houses[i+1]["Favorite Sport"]
        if occ == "teacher":
            if sport_next is not None and sport_next != "soccer":
                return False
        if sport_next == "soccer":
            if houses[i]["Occupation"] is not None and houses[i]["Occupation"] != "teacher":
                return False

    # C16. The rabbit owner is Alice.
    for i in range(num_assigned):
        name = houses[i]["Name"]
        animal = houses[i]["Animal"]
        if animal == "rabbit":
            if name is not None and name != "Alice":
                return False
        if name == "Alice":
            if animal is not None and animal != "rabbit":
                return False

    # C17. The fish enthusiast is Carol.
    for i in range(num_assigned):
        name = houses[i]["Name"]
        animal = houses[i]["Animal"]
        if animal == "fish":
            if name is not None and name != "Carol":
                return False
        if name == "Carol":
            if animal is not None and animal != "fish":
                return False

    # C18. The person who loves baseball is in the first house.
    if num_assigned > 0:
        if houses[0]["Favorite Sport"] is not None and houses[0]["Favorite Sport"] != "baseball":
            return False

    # C19. The cat lover is somewhere to the right of the person who is very short.
    idx_cat = None
    idx_vshort = None
    for i in range(num_assigned):
        if houses[i]["Animal"] == "cat":
            idx_cat = i
        if houses[i]["Height"] == "very short":
            idx_vshort = i
    if idx_cat is not None and idx_vshort is not None:
        if idx_cat <= idx_vshort:
            return False

    # C20. The person who is super tall is in the fifth house.
    if num_assigned > 4:
        if houses[4]["Height"] is not None and houses[4]["Height"] != "super tall":
            return False

    return True

def backtrack(i, houses, rem_names, rem_animals, rem_occ, rem_sports, rem_heights, solutions):
    if i == len(houses):
        if check_constraints(houses, len(houses)):
            solutions.append([house.copy() for house in houses])
        return

    # Identify which attributes in house i still need an assignment.
    free_keys = []
    for key in ["Name", "Animal", "Occupation", "Favorite Sport", "Height"]:
        if houses[i][key] is None:
            free_keys.append(key)

    # If no free keys, check constraints and move to next house.
    if not free_keys:
        if check_constraints(houses, i+1):
            backtrack(i+1, houses, rem_names, rem_animals, rem_occ, rem_sports, rem_heights, solutions)
        return

    # Build domains for each free key from the remaining sets.
    domains = {}
    for key in free_keys:
        if key == "Name":
            domains[key] = list(rem_names)
        elif key == "Animal":
            domains[key] = list(rem_animals)
        elif key == "Occupation":
            domains[key] = list(rem_occ)
        elif key == "Favorite Sport":
            domains[key] = list(rem_sports)
        elif key == "Height":
            domains[key] = list(rem_heights)

    # Try every combination of values for the free keys.
    for selection in product(*(domains[k] for k in free_keys)):
        backup = {}
        for idx, key in enumerate(free_keys):
            backup[key] = houses[i][key]
            houses[i][key] = selection[idx]
        if not check_constraints(houses, i+1):
            for key in free_keys:
                houses[i][key] = backup[key]
            continue
        # Update remaining sets for the next recursion.
        new_rem_names = rem_names.copy()
        new_rem_animals = rem_animals.copy()
        new_rem_occ = rem_occ.copy()
        new_rem_sports = rem_sports.copy()
        new_rem_heights = rem_heights.copy()
        for key in free_keys:
            val = houses[i][key]
            if key == "Name" and val in new_rem_names:
                new_rem_names.remove(val)
            elif key == "Animal" and val in new_rem_animals:
                new_rem_animals.remove(val)
            elif key == "Occupation" and val in new_rem_occ:
                new_rem_occ.remove(val)
            elif key == "Favorite Sport" and val in new_rem_sports:
                new_rem_sports.remove(val)
            elif key == "Height" and val in new_rem_heights:
                new_rem_heights.remove(val)
        backtrack(i+1, houses, new_rem_names, new_rem_animals, new_rem_occ, new_rem_sports, new_rem_heights, solutions)
        # Undo assignment.
        for key in free_keys:
            houses[i][key] = backup[key]

def main():
    # Initialize 6 houses with keys.
    houses = []
    for i in range(6):
        houses.append({
            "House": str(i+1),
            "Name": None,
            "Animal": None,
            "Occupation": None,
            "Favorite Sport": None,
            "Height": None
        })
    # Fixed assignments based on clues:
    # Clue 18: The person who loves baseball is in the first house.
    houses[0]["Favorite Sport"] = "baseball"
    # Clue 12 & 1: The person who loves baseball is directly left of the engineer, and the engineer is the dog owner.
    houses[1]["Occupation"] = "engineer"
    houses[1]["Animal"] = "dog"
    # Clues 15, 10, 6: The teacher (who loves tennis and keeps horses) is directly left of the person who loves soccer.
    # There is only one possibility: Teacher in house 3 and soccer-lover in house 4.
    houses[2]["Occupation"] = "teacher"
    houses[2]["Favorite Sport"] = "tennis"
    houses[2]["Animal"] = "horse"
    houses[3]["Name"] = "Carol"  # Clue 7: Carol is the person who loves soccer.
    houses[3]["Favorite Sport"] = "soccer"
    houses[3]["Animal"] = "fish"   # Clue 17: The fish enthusiast is Carol.
    # Clue 9 & 20: The lawyer is in the fifth house and the person who is super tall is in the fifth house.
    houses[4]["Occupation"] = "lawyer"
    houses[4]["Height"] = "super tall"
    # House 6 remains completely free.

    # Remaining domains after fixed assignments.
    rem_names = {"Arnold", "Peter", "Bob", "Eric", "Alice"}
    rem_animals = {"rabbit", "cat", "bird"}
    rem_occ = {"nurse", "artist", "doctor"}
    rem_sports = {"volleyball", "basketball", "swimming"}
    rem_heights = {"average", "tall", "short", "very short", "very tall"}

    solutions = []
    backtrack(0, houses, rem_names, rem_animals, rem_occ, rem_sports, rem_heights, solutions)

    # Build the output in the required JSON structure.
    header = ["House", "Name", "Animal", "Occupation", "Favorite Sport", "Height"]
    if solutions:
        # Use the first found solution.
        sol = solutions[0]
        rows = []
        for house in sol:
            row = [house["House"], house["Name"], house["Animal"], house["Occupation"], house["Favorite Sport"], house["Height"]]
            rows.append(row)
    else:
        rows = []
    output = {"solution": {"header": header, "rows": rows}}
    print(json.dumps(output))

if __name__ == "__main__":
    main()