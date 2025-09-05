import json
import itertools

def main():
    # Define the attributes for the houses
    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    pets = ["cat", "dog"]
    heights = ["short", "very short"]
    
    houses_count = 2
    solution = None

    # Iterate through all possible assignments (permutations for each attribute)
    for name_perm in itertools.permutations(names, houses_count):
        for hobby_perm in itertools.permutations(hobbies, houses_count):
            for pet_perm in itertools.permutations(pets, houses_count):
                for height_perm in itertools.permutations(heights, houses_count):
                    # Build candidate solution for the houses (house numbers 1 and 2)
                    candidate = []
                    for i in range(houses_count):
                        candidate.append({
                            "House": str(i + 1),
                            "Name": name_perm[i],
                            "Hobby": hobby_perm[i],
                            "Pet": pet_perm[i],
                            "Height": height_perm[i]
                        })
                    
                    # Constraint 1: The person who is very short is the photography enthusiast.
                    valid = True
                    for house in candidate:
                        if house["Height"] == "very short" and house["Hobby"] != "photography":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Constraint 2: Eric is the person who is very short.
                    found_eric = False
                    for house in candidate:
                        if house["Name"] == "Eric":
                            if house["Height"] != "very short":
                                valid = False
                            else:
                                found_eric = True
                            break
                    if not valid or not found_eric:
                        continue

                    # Constraint 3: The person who has a cat is somewhere to the right of the person who is very short.
                    index_vs = None
                    index_cat = None
                    for idx, house in enumerate(candidate):
                        if house["Height"] == "very short":
                            index_vs = idx
                        if house["Pet"] == "cat":
                            index_cat = idx
                    if index_vs is None or index_cat is None or index_cat <= index_vs:
                        continue
                    
                    # All constraints satisfied for this candidate.
                    solution = candidate
                    break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    if solution is None:
        # In case no solution is found (shouldn't happen with these constraints)
        output = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Pet", "Height"],
                "rows": []
            }
        }
    else:
        # Build the output rows from the solution candidate
        rows = []
        # Ensure houses are in the correct order (House "1" then "2")
        solution.sort(key=lambda h: int(h["House"]))
        for house in solution:
            rows.append([house["House"], house["Name"], house["Hobby"], house["Pet"], house["Height"]])
        
        output = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Pet", "Height"],
                "rows": rows
            }
        }

    print(json.dumps(output))

if __name__ == "__main__":
    main()