#!/usr/bin/env python3
import json

# Global attribute values
NAMES = ["Arnold", "Peter", "Bob", "Eric", "Carol", "Alice"]
ANIMALS = ["horse", "rabbit", "fish", "cat", "bird", "dog"]
OCCUPATIONS = ["engineer", "nurse", "lawyer", "teacher", "artist", "doctor"]
SPORTS = ["basketball", "volleyball", "soccer", "tennis", "baseball", "swimming"]
HEIGHTS = ["average", "tall", "short", "very short", "very tall", "super tall"]

# Fixed constraints by house index (0-indexed)
FIXED = {
    0: {"FavoriteSport": "baseball"},
    1: {"Occupation": "engineer"},
    4: {"Occupation": "lawyer", "Height": "super tall"}
}

def check_global(assignment):
    # assignment is a list of dictionaries for houses with indices 0..len(assignment)-1.
    n = len(assignment)
    
    # Clue 2: The person with average height is somewhere to the left of the person who is short.
    for i, house in enumerate(assignment):
        if house["Height"] == "short":
            if i == 0:
                return False
            if not any(assignment[j]["Height"] == "average" for j in range(i)):
                return False

    # Clue 4: The person who is tall is somewhere to the left of the person who is very short.
    for i, house in enumerate(assignment):
        if house["Height"] == "very short":
            if i == 0:
                return False
            if not any(assignment[j]["Height"] == "tall" for j in range(i)):
                return False

    # Clue 19: The cat lover is somewhere to the right of the person who is very short.
    for i, house in enumerate(assignment):
        if house["Animal"] == "cat":
            if i == 0:
                return False
            if not any(assignment[j]["Height"] == "very short" for j in range(i)):
                return False

    # Clue 3: The person who has an average height is directly left of the rabbit owner.
    # Check for every adjacent assigned pair.
    for i in range(len(assignment)-1):
        if assignment[i]["Height"] == "average" and assignment[i+1]["Animal"] != "rabbit":
            return False
        if assignment[i+1]["Animal"] == "rabbit" and assignment[i]["Height"] != "average":
            return False

    # Clue 12: The person who loves baseball is directly left of the person who is an engineer.
    for i in range(len(assignment)-1):
        if assignment[i]["FavoriteSport"] == "baseball" and assignment[i+1]["Occupation"] != "engineer":
            return False
        if assignment[i+1]["Occupation"] == "engineer" and assignment[i]["FavoriteSport"] != "baseball":
            return False

    # Clue 15: The person who is a teacher is directly left of the person who loves soccer.
    for i in range(len(assignment)-1):
        if assignment[i]["Occupation"] == "teacher" and assignment[i+1]["FavoriteSport"] != "soccer":
            return False

    # Clue 14: Bob is somewhere to the right of the person who is an artist.
    for i, house in enumerate(assignment):
        if house["Name"] == "Bob":
            if i == 0:
                return False
            if not any(assignment[j]["Occupation"] == "artist" for j in range(i)):
                return False

    # Clue 9: The person who is a lawyer is in the fifth house.
    if len(assignment) > 4:
        if assignment[4]["Occupation"] != "lawyer":
            return False

    # Clue 18: The person who loves baseball is in the first house.
    if len(assignment) > 0:
        if assignment[0]["FavoriteSport"] != "baseball":
            return False

    # Clue 20: The person who is super tall is in the fifth house.
    if len(assignment) > 4:
        if assignment[4]["Height"] != "super tall":
            return False

    # Additional bidirectional constraints already checked in candidate level.
    return True

def search(assignment, used_names, used_animals, used_occs, used_sports, used_heights):
    if len(assignment) == 6:
        # Full assignment: check global constraints one last time.
        if check_global(assignment):
            return assignment
        else:
            return None

    i = len(assignment)  # current house index (0-indexed)
    # Loop over remaining options for each attribute.
    for name in [n for n in NAMES if n not in used_names]:
        for animal in [a for a in ANIMALS if a not in used_animals]:
            for occ in [o for o in OCCUPATIONS if o not in used_occs]:
                for sport in [s for s in SPORTS if s not in used_sports]:
                    for height in [h for h in HEIGHTS if h not in used_heights]:
                        candidate = {
                            "Name": name,
                            "Animal": animal,
                            "Occupation": occ,
                            "FavoriteSport": sport,
                            "Height": height
                        }
                        # Enforce fixed house constraints.
                        if i in FIXED:
                            fixed_attrs = FIXED[i]
                            for key, fixed_val in fixed_attrs.items():
                                if candidate[key] != fixed_val:
                                    continue
                            # If candidate doesn't match one of the fixed constraints, skip.
                            for key in FIXED[i]:
                                if candidate[key] != FIXED[i][key]:
                                    continue
                        # Additional fixed position: if teacher is in last house (i==5) it's invalid because clue 15 requires a neighbor.
                        if i == 5 and candidate["Occupation"] == "teacher":
                            continue

                        # Candidate-specific constraints:
                        validCandidate = True
                        # Clue 5: Arnold is the cat lover.
                        if candidate["Name"] == "Arnold" and candidate["Animal"] != "cat":
                            validCandidate = False
                        # Clue 7: Carol is the person who loves soccer.
                        if candidate["Name"] == "Carol" and candidate["FavoriteSport"] != "soccer":
                            validCandidate = False
                        # Clue 11: The person who has an average height is the person who loves swimming.
                        if candidate["Height"] == "average" and candidate["FavoriteSport"] != "swimming":
                            validCandidate = False
                        if candidate["FavoriteSport"] == "swimming" and candidate["Height"] != "average":
                            validCandidate = False
                        # Clue 8: The person who is tall is the person who loves volleyball.
                        if candidate["Height"] == "tall" and candidate["FavoriteSport"] != "volleyball":
                            validCandidate = False
                        if candidate["FavoriteSport"] == "volleyball" and candidate["Height"] != "tall":
                            validCandidate = False
                        # Clues 6 & 10: Teacher must have horses and love tennis.
                        if candidate["Occupation"] == "teacher":
                            if candidate["Animal"] != "horse" or candidate["FavoriteSport"] != "tennis":
                                validCandidate = False
                        if candidate["Animal"] == "horse" or candidate["FavoriteSport"] == "tennis":
                            if candidate["Occupation"] != "teacher":
                                validCandidate = False
                        # Clue 13: Peter is the nurse.
                        if candidate["Name"] == "Peter" and candidate["Occupation"] != "nurse":
                            validCandidate = False
                        # Clue 16: The rabbit owner is Alice.
                        if candidate["Name"] == "Alice" and candidate["Animal"] != "rabbit":
                            validCandidate = False
                        if candidate["Animal"] == "rabbit" and candidate["Name"] != "Alice":
                            validCandidate = False
                        # Clue 17: The fish enthusiast is Carol.
                        if candidate["Name"] == "Carol" and candidate["Animal"] != "fish":
                            validCandidate = False
                        if candidate["Animal"] == "fish" and candidate["Name"] != "Carol":
                            validCandidate = False
                        # Clue 1: The engineer is the dog owner.
                        if candidate["Occupation"] == "engineer" and candidate["Animal"] != "dog":
                            validCandidate = False
                        if candidate["Animal"] == "dog" and candidate["Occupation"] != "engineer":
                            validCandidate = False
                        # Clue 14: Bob is somewhere to the right of the person who is an artist.
                        if candidate["Name"] == "Bob":
                            if i == 0 or not any(h["Occupation"] == "artist" for h in assignment):
                                validCandidate = False

                        # Neighbor constraints (with the immediately previous house)
                        if i > 0:
                            prev = assignment[-1]
                            # Clue 3: The person who has an average height is directly left of the rabbit owner.
                            if prev["Height"] == "average" and candidate["Animal"] != "rabbit":
                                validCandidate = False
                            if candidate["Animal"] == "rabbit" and prev["Height"] != "average":
                                validCandidate = False
                            # Clue 12: The person who loves baseball is directly left of the person who is an engineer.
                            if prev["FavoriteSport"] == "baseball" and candidate["Occupation"] != "engineer":
                                validCandidate = False
                            if candidate["Occupation"] == "engineer" and prev["FavoriteSport"] != "baseball":
                                validCandidate = False
                            # Clue 15: The person who is a teacher is directly left of the person who loves soccer.
                            if prev["Occupation"] == "teacher" and candidate["FavoriteSport"] != "soccer":
                                validCandidate = False

                        if not validCandidate:
                            continue

                        new_assignment = assignment + [candidate]
                        if not check_global(new_assignment):
                            continue

                        new_used_names = used_names | {name}
                        new_used_animals = used_animals | {animal}
                        new_used_occs = used_occs | {occ}
                        new_used_sports = used_sports | {sport}
                        new_used_heights = used_heights | {height}

                        result = search(new_assignment, new_used_names, new_used_animals, new_used_occs, new_used_sports, new_used_heights)
                        if result is not None:
                            return result
    return None

def main():
    solution = search([], set(), set(), set(), set(), set())
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"], "rows": []}}
    else:
        rows = []
        for idx, house in enumerate(solution):
            # House numbers are 1-indexed as strings.
            row = [
                str(idx+1),
                house["Name"],
                house["Animal"],
                house["Occupation"],
                house["FavoriteSport"],
                house["Height"]
            ]
            rows.append(row)
        output = {"solution": {"header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"], "rows": rows}}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()