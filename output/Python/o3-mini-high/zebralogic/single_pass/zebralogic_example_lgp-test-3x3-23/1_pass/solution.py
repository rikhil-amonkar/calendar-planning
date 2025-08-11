#!/usr/bin/env python3
import json
import itertools

def satisfies_constraints(houses):
    # houses is a list of dictionaries for house positions 0,1,2 representing houses 1,2,3 respectively.

    # Helper: find index by condition
    def find_index(key, value):
        for i, house in enumerate(houses):
            if house[key] == value:
                return i
        return None

    # Constraint 1: The person who is a doctor and Eric are next to each other.
    doc_index = find_index("Occupation", "doctor")
    eric_index = find_index("Name", "Eric")
    if doc_index is None or eric_index is None or abs(doc_index - eric_index) != 1:
        return False

    # Constraint 2: The person who loves cooking is directly left of the person who is a teacher.
    pair_found = False
    for i in range(len(houses) - 1):
        if houses[i]["Hobby"] == "cooking" and houses[i+1]["Occupation"] == "teacher":
            pair_found = True
            break
    if not pair_found:
        return False

    # Constraint 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening.
    garden_index = find_index("Hobby", "gardening")
    if garden_index is None or doc_index <= garden_index:
        return False

    # Constraint 4: The photography enthusiast is the person who is a teacher.
    for house in houses:
        if house["Occupation"] == "teacher" and house["Hobby"] != "photography":
            return False
        if house["Hobby"] == "photography" and house["Occupation"] != "teacher":
            return False

    # Constraint 5: The person who is an engineer is Peter.
    for house in houses:
        if house["Occupation"] == "engineer" and house["Name"] != "Peter":
            return False
        if house["Name"] == "Peter" and house["Occupation"] != "engineer":
            return False

    return True

def main():
    # Define the possible values for each attribute.
    house_numbers = [1, 2, 3]
    names = ["Peter", "Arnold", "Eric"]
    occupations = ["doctor", "teacher", "engineer"]
    hobbies = ["cooking", "photography", "gardening"]

    solution = None

    # Permute each category separately.
    for name_perm in itertools.permutations(names):
        for occ_perm in itertools.permutations(occupations):
            for hobby_perm in itertools.permutations(hobbies):
                # Build houses data structure: list of dictionaries with keys: House, Name, Occupation, Hobby
                houses = []
                for i in range(3):
                    house = {
                        "House": str(house_numbers[i]),
                        "Name": name_perm[i],
                        "Occupation": occ_perm[i],
                        "Hobby": hobby_perm[i]
                    }
                    houses.append(house)
                # Check if this assignment satisfies all constraints.
                if satisfies_constraints(houses):
                    solution = houses
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    # Prepare the output JSON structure.
    output = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Hobby"],
            "rows": [[house["House"], house["Name"], house["Occupation"], house["Hobby"]] for house in solution]
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()