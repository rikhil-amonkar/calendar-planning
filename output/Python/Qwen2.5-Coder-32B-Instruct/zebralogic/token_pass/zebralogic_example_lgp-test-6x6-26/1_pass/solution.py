import json
from itertools import permutations

# Initialize houses with None values
houses = [{attr: None for attr in ["Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"]} for _ in range(6)]

# Define all possible values for each attribute
names = ["Peter", "Carol", "Eric", "Alice", "Bob", "Arnold"]
phone_models = ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"]
cigars = ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"]
flowers = ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"]
colors = ["yellow", "red", "green", "blue", "white", "purple"]
favorite_sports = ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"]

# Function to check if a permutation satisfies all constraints
def is_valid_solution(houses):
    # Constraint 1
    if houses[1]["PhoneModel"] != "oneplus 9":
        return False
    # Constraint 2
    if not any(houses[i]["PhoneModel"] == "xiaomi mi 11" and houses[j]["PhoneModel"] == "huawei p50" and i < j for i in range(6) for j in range(6)):
        return False
    # Constraint 3
    if not any(house["Name"] == "Carol" and house["Flower"] == "carnations" for house in houses):
        return False
    # Constraint 4
    if not any(houses[i]["Color"] == "purple" and houses[i+1]["Cigar"] == "pall mall" for i in range(5)):
        return False
    # Constraint 5
    if not any(house["Color"] == "green" and house["Cigar"] == "blue master" for house in houses):
        return False
    # Constraint 6
    if not any(houses[i]["Color"] == "yellow" and houses[i+1]["Color"] == "blue" for i in range(5)) and \
       not any(houses[i]["Color"] == "blue" and houses[i+1]["Color"] == "yellow" for i in range(5)):
        return False
    # Constraint 7
    if not any(houses[i]["PhoneModel"] == "samsung galaxy s21" and houses[j]["Name"] == "Eric" and i < j for i in range(6) for j in range(6)):
        return False
    # Constraint 8
    if not any(houses[i]["Name"] == "Carol" and houses[j]["Flower"] == "daffodils" and abs(i - j) == 2 for i in range(6) for j in range(6)):
        return False
    # Constraint 9
    if not any(house["Cigar"] == "prince" and house["FavoriteSport"] == "basketball" for house in houses):
        return False
    # Constraint 10
    if not any(house["Cigar"] == "dunhill" and house["FavoriteSport"] == "volleyball" for house in houses):
        return False
    # Constraint 11
    if not any(house["FavoriteSport"] == "swimming" and house["PhoneModel"] == "google pixel 6" for house in houses):
        return False
    # Constraint 12
    if not any(houses[i]["PhoneModel"] == "huawei p50" and houses[i+1]["Color"] == "white" for i in range(5)):
        return False
    # Constraint 13
    if not any(houses[i]["PhoneModel"] == "oneplus 9" and houses[i+1]["Flower"] == "roses" for i in range(5)) and \
       not any(houses[i]["Flower"] == "roses" and houses[i+1]["PhoneModel"] == "oneplus 9" for i in range(5)):
        return False
    # Constraint 14
    if not any(houses[i]["Flower"] == "iris" and houses[j]["Name"] == "Eric" and i < j for i in range(6) for j in range(6)):
        return False
    # Constraint 15
    if not any(house["Name"] == "Peter" and house["Cigar"] == "dunhill" for house in houses):
        return False
    # Constraint 16
    if not any(house["Name"] == "Peter" and house["Color"] == "blue" for house in houses):
        return False
    # Constraint 17
    if not any(house["Name"] == "Bob" and house["Flower"] == "tulips" for house in houses):
        return False
    # Constraint 18
    if houses[0]["Name"] != "Alice":
        return False
    # Constraint 19
    if not any(houses[i]["Cigar"] == "blue master" and houses[i+1]["FavoriteSport"] == "baseball" for i in range(5)):
        return False
    # Constraint 20
    if not any(houses[i]["PhoneModel"] == "google pixel 6" and houses[j]["Cigar"] == "blends" and i > j for i in range(6) for j in range(6)):
        return False
    # Constraint 21
    if not any(house["Name"] == "Carol" and house["FavoriteSport"] == "soccer" for house in houses):
        return False
    # Constraint 22
    if not any(houses[i]["Flower"] == "carnations" and houses[i+1]["Cigar"] == "blends" for i in range(5)):
        return False
    # Constraint 23
    if not any(house["Name"] == "Eric" and house["Cigar"] == "blends" for house in houses):
        return False
    # Constraint 24
    if not any(houses[i]["Flower"] == "iris" and houses[j]["Name"] == "Eric" and i < j for i in range(6) for j in range(6)):
        return False
    # Constraint 25
    if not any(house["PhoneModel"] == "iphone 13" and house["FavoriteSport"] == "volleyball" for house in houses):
        return False
    
    return True

# Generate all permutations and find a valid solution
for name_perm in permutations(names):
    for phone_model_perm in permutations(phone_models):
        for cigar_perm in permutations(cigars):
            for flower_perm in permutations(flowers):
                for color_perm in permutations(colors):
                    for favorite_sport_perm in permutations(favorite_sports):
                        for i in range(6):
                            houses[i]["Name"] = name_perm[i]
                            houses[i]["PhoneModel"] = phone_model_perm[i]
                            houses[i]["Cigar"] = cigar_perm[i]
                            houses[i]["Flower"] = flower_perm[i]
                            houses[i]["Color"] = color_perm[i]
                            houses[i]["FavoriteSport"] = favorite_sport_perm[i]
                        if is_valid_solution(houses):
                            break
                    else:
                        continue
                    break
                else:
                    continue
                break
            else:
                continue
            break
        else:
            continue
        break

# Prepare the solution in the required JSON format
solution_dict = {
    "solution": {
        "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
        "rows": [[str(i+1)] + [houses[i][attr] for attr in ["Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"]] for i in range(6)]
    }
}

# Output the solution as JSON
print(json.dumps(solution_dict, indent=2))