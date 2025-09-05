#!/usr/bin/env python3
import json
import sys

# Define the full sets for each category.
NAMES = ["Arnold", "Peter", "Bob", "Eric", "Carol", "Alice"]
ANIMALS = ["horse", "rabbit", "fish", "cat", "bird", "dog"]
OCCUPATIONS = ["engineer", "nurse", "lawyer", "teacher", "artist", "doctor"]
SPORTS = ["basketball", "volleyball", "soccer", "tennis", "baseball", "swimming"]
HEIGHTS = ["average", "tall", "short", "very short", "very tall", "super tall"]

# Each house is represented as a dictionary with keys:
# "House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"
# Houses are indexed 0 to 5 (representing houses 1 to 6).

def check_relative_constraints(solution):
    # solution is a list of length (number of houses assigned so far)
    n = len(solution)

    # Helper: get index for a given value in a given key if assigned.
    def get_index(key, value):
        for idx, house in enumerate(solution):
            if house.get(key) == value:
                return idx
        return None

    # Constraint 2: Average height is to the left of the person who is short.
    avg_index = get_index("Height", "average")
    short_index = get_index("Height", "short")
    if avg_index is not None and short_index is not None:
        if not (avg_index < short_index):
            return False

    # Constraint 3: Average height is directly left of the rabbit owner.
    for i in range(n):
        house = solution[i]
        if house.get("Height") == "average":
            if i + 1 < n:
                # if next house has an animal assigned, it must be rabbit.
                if solution[i+1].get("Animal") is not None:
                    if solution[i+1].get("Animal") != "rabbit":
                        return False
        if house.get("Animal") == "rabbit":
            if i - 1 >= 0:
                if solution[i-1].get("Height") is not None:
                    if solution[i-1].get("Height") != "average":
                        return False

    # Constraint 4: The person who is tall is somewhere to the left of the person who is very short.
    tall_index = get_index("Height", "tall")
    vshort_index = get_index("Height", "very short")
    if tall_index is not None and vshort_index is not None:
        if not (tall_index < vshort_index):
            return False

    # Constraint 12: Baseball is directly left of the engineer.
    for i in range(n):
        house = solution[i]
        if house.get("FavoriteSport") == "baseball":
            if i + 1 < n:
                if solution[i+1].get("Occupation") is not None:
                    if solution[i+1].get("Occupation") != "engineer":
                        return False
        if house.get("Occupation") == "engineer":
            if i - 1 >= 0:
                if solution[i-1].get("FavoriteSport") is not None:
                    if solution[i-1].get("FavoriteSport") != "baseball":
                        return False

    # Constraint 14: Bob is somewhere to the right of the person who is an artist.
    bob_index = None
    artist_index = None
    for i, house in enumerate(solution):
        if house.get("Name") == "Bob":
            bob_index = i
        if house.get("Occupation") == "artist":
            artist_index = i
    if bob_index is not None and artist_index is not None:
        if not (artist_index < bob_index):
            return False

    # Constraint 15: The teacher is directly left of the person who loves soccer.
    for i in range(n):
        house = solution[i]
        if house.get("Occupation") == "teacher":
            if i + 1 < n:
                if solution[i+1].get("FavoriteSport") is not None:
                    if solution[i+1].get("FavoriteSport") != "soccer":
                        return False
        if house.get("FavoriteSport") == "soccer":
            if i - 1 >= 0:
                if solution[i-1].get("Occupation") is not None:
                    if solution[i-1].get("Occupation") != "teacher":
                        return False

    # Constraint 19: The cat lover is somewhere to the right of the person who is very short.
    cat_index = None
    vshort_index = get_index("Height", "very short")
    for i, house in enumerate(solution):
        if house.get("Animal") == "cat":
            cat_index = i
            break
    if cat_index is not None and vshort_index is not None:
        if not (vshort_index < cat_index):
            return False

    return True

def check_house_constraints(house, index):
    # Check constraints that refer to a single house by itself.
    # index is the house index (0-based)
    # We assume if a value is not yet assigned (None), we skip the check.
    # Constraint 1: Engineer is dog owner.
    occ = house.get("Occupation")
    animal = house.get("Animal")
    if occ == "engineer" and animal is not None:
        if animal != "dog":
            return False
    if animal == "dog" and occ is not None:
        if occ != "engineer":
            return False

    # Constraint 5: Arnold is the cat lover.
    name = house.get("Name")
    if name == "Arnold" and animal is not None:
        if animal != "cat":
            return False
    if animal == "cat" and name is not None:
        if name != "Arnold":
            return False

    # Constraint 6: The person who keeps horses is the teacher.
    if animal == "horse" and occ is not None:
        if occ != "teacher":
            return False
    if occ == "teacher" and animal is not None:
        if animal != "horse":
            return False

    # Constraint 7: Carol is the person who loves soccer.
    sport = house.get("FavoriteSport")
    if name == "Carol" and sport is not None:
        if sport != "soccer":
            return False
    if sport == "soccer" and name is not None:
        if name != "Carol":
            return False

    # Constraint 8: The person who is tall is the one who loves volleyball.
    height = house.get("Height")
    if height == "tall" and sport is not None:
        if sport != "volleyball":
            return False
    if sport == "volleyball" and height is not None:
        if height != "tall":
            return False

    # Constraint 9: The lawyer is in the fifth house (index 4).
    if index == 4:
        if occ is not None and occ != "lawyer":
            return False
    else:
        if occ == "lawyer":
            return False

    # Constraint 10: The person who loves tennis is the teacher.
    if sport == "tennis" and occ is not None:
        if occ != "teacher":
            return False
    if occ == "teacher" and sport is not None:
        if sport != "tennis":
            return False

    # Constraint 11: The person who has an average height loves swimming.
    if height == "average" and sport is not None:
        if sport != "swimming":
            return False
    if sport == "swimming" and height is not None:
        if height != "average":
            return False

    # Constraint 13: Peter is the nurse.
    if name == "Peter" and occ is not None:
        if occ != "nurse":
            return False
    if occ == "nurse" and name is not None:
        if name != "Peter":
            return False

    # Constraint 16: The rabbit owner is Alice.
    if animal == "rabbit" and name is not None:
        if name != "Alice":
            return False
    if name == "Alice" and animal is not None:
        if animal != "rabbit":
            return False

    # Constraint 17: The fish enthusiast is Carol.
    if animal == "fish" and name is not None:
        if name != "Carol":
            return False
    if name == "Carol" and animal is not None:
        if animal != "fish":
            return False

    # Constraint 18: The person who loves baseball is in the first house.
    if index == 0:
        if sport is not None and sport != "baseball":
            return False
    else:
        # For houses other than the first, they must not have baseball if already fixed by other relation (but baseball is assigned uniquely)
        pass

    # Constraint 20: The person who is super tall is in the fifth house.
    if index == 4:
        if height is not None and height != "super tall":
            return False
    else:
        if height == "super tall":
            return False

    return True

def check_all_uniqueness(solution):
    # Check that for each attribute each value appears at most once.
    keys = ["Name", "Animal", "Occupation", "FavoriteSport", "Height"]
    for key in keys:
        seen = []
        for house in solution:
            val = house.get(key)
            if val is not None:
                if val in seen:
                    return False
                seen.append(val)
    return True

def is_valid(solution):
    # First check uniqueness
    if not check_all_uniqueness(solution):
        return False
    # Check constraints for each assigned house individually.
    for idx, house in enumerate(solution):
        if not check_house_constraints(house, idx):
            return False
    # Check relative order constraints.
    if not check_relative_constraints(solution):
        return False
    return True

def backtrack(index, solution, rem_names, rem_animals, rem_occs, rem_sports, rem_heights):
    if index == 6:
        # Complete solution, check validity one more time.
        if is_valid(solution):
            return solution
        return None

    # Prepare domain restrictions for this house based on fixed clues.
    # For House 1 (index 0): FavoriteSport must be "baseball"
    # For House 2 (index 1): Occupation must be "engineer"
    # For House 5 (index 4): Height must be "super tall"
    domain_names = rem_names[:]
    domain_animals = rem_animals[:]
    domain_occs = rem_occs[:]
    domain_sports = rem_sports[:]
    domain_heights = rem_heights[:]

    if index == 0:
        if "baseball" in domain_sports:
            domain_sports = ["baseball"]
        else:
            return None
    if index == 1:
        if "engineer" in domain_occs:
            domain_occs = ["engineer"]
        else:
            return None
    if index == 4:
        if "super tall" in domain_heights:
            domain_heights = ["super tall"]
        else:
            return None

    # Try all combinations from the current domains.
    for name in domain_names:
        for animal in domain_animals:
            for occ in domain_occs:
                for sport in domain_sports:
                    for height in domain_heights:
                        house = {
                            "House": str(index + 1),
                            "Name": name,
                            "Animal": animal,
                            "Occupation": occ,
                            "FavoriteSport": sport,
                            "Height": height
                        }
                        # Check constraints for this house.
                        if not check_house_constraints(house, index):
                            continue

                        # Tentatively add this house.
                        new_solution = solution + [house]

                        # Check if uniqueness holds and relative order constraints for the partial solution.
                        if not is_valid(new_solution):
                            continue

                        # Update remaining sets
                        new_rem_names = rem_names[:]
                        new_rem_animals = rem_animals[:]
                        new_rem_occs = rem_occs[:]
                        new_rem_sports = rem_sports[:]
                        new_rem_heights = rem_heights[:]

                        new_rem_names.remove(name)
                        new_rem_animals.remove(animal)
                        new_rem_occs.remove(occ)
                        new_rem_sports.remove(sport)
                        new_rem_heights.remove(height)

                        result = backtrack(index + 1, new_solution, new_rem_names, new_rem_animals, new_rem_occs, new_rem_sports, new_rem_heights)
                        if result is not None:
                            return result
    return None

def main():
    sol = backtrack(0, [],
                    NAMES[:],
                    ANIMALS[:],
                    OCCUPATIONS[:],
                    SPORTS[:],
                    HEIGHTS[:])
    if sol is None:
        print("No solution found", file=sys.stderr)
        sys.exit(1)
    # Prepare the solution in required JSON format.
    result = {
        "solution": {
            "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
            "rows": []
        }
    }
    # Order the houses by their house number (they are in order already).
    for house in sol:
        row = [
            house["House"],
            house["Name"],
            house["Animal"],
            house["Occupation"],
            house["FavoriteSport"],
            house["Height"]
        ]
        result["solution"]["rows"].append(row)
    # Output the JSON.
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()