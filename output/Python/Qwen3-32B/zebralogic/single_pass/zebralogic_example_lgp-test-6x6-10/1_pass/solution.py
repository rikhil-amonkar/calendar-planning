import json
from itertools import permutations

# Define all categories and their possible values
names = ["Arnold", "Bob", "Peter", "Alice", "Carol", "Eric"]
foods = ["stew", "grilled cheese", "stir fry", "soup", "pizza", "spaghetti"]
heights = ["tall", "average", "super tall", "very short", "very tall", "short"]
drinks = ["root beer", "boba tea", "coffee", "water", "tea", "milk"]
pets = ["hamster", "fish", "cat", "dog", "bird", "rabbit"]
phones = ["samsung galaxy s21", "xiaomi mi 11", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9"]

# Fixed values based on clues
fixed_phone_house3 = "iphone 13"
fixed_food_house2 = "soup"
fixed_carol_phone = "samsung galaxy s21"
fixed_arnold_phone = "oneplus 9"
fixed_bob_height = "tall"
fixed_grilled_cheese_person = "Bob"
fixed_arnold_height = "very tall"
fixed_carol_height = None  # will be determined

def check_solution(houses):
    # Check all clues
    # 1. The person who uses an iPhone 13 is in the third house.
    if houses[2]["PhoneModel"] != "iphone 13":
        return False
    
    # 2. Bob is the person who is tall.
    bob_index = next(i for i, h in enumerate(houses) if h["Name"] == "Bob")
    if houses[bob_index]["Height"] != "tall":
        return False
    
    # 3. The person who loves the soup is in the second house.
    if houses[1]["Food"] != "soup":
        return False
    
    # 4. The root beer lover is directly left of the person who uses a Xiaomi Mi 11.
    for i in range(5):
        if houses[i]["Drink"] == "root beer" and houses[i+1]["PhoneModel"] == "xiaomi mi 11":
            break
    else:
        return False
    
    # 5. The person who uses a Huawei P50 is directly left of the person who loves eating grilled cheese.
    for i in range(5):
        if houses[i]["PhoneModel"] == "huawei p50" and houses[i+1]["Food"] == "grilled cheese":
            break
    else:
        return False
    
    # 6. The person who loves stir fry is the person who likes milk.
    for h in houses:
        if h["Food"] == "stir fry" and h["Drink"] != "milk":
            return False
    
    # 7. The person who loves grilled cheese is the person who is tall.
    grilled_cheese_index = next(i for i, h in enumerate(houses) if h["Food"] == "grilled cheese")
    if houses[grilled_cheese_index]["Height"] != "tall":
        return False
    
    # 8. The person who uses a Xiaomi Mi 11 is the coffee drinker.
    for h in houses:
        if h["PhoneModel"] == "xiaomi mi 11" and h["Drink"] != "coffee":
            return False
    
    # 9. The person who uses a OnePlus 9 is Arnold.
    arnold_index = next(i for i, h in enumerate(houses) if h["Name"] == "Arnold")
    if houses[arnold_index]["PhoneModel"] != "oneplus 9":
        return False
    
    # 10. The person with a rabbit is not in the fifth house.
    if houses[4]["Pet"] == "rabbit":
        return False
    
    # 11. The person with a hamster is somewhere to the right of the person who uses a Google Pixel 6.
    google_pixel_index = next(i for i, h in enumerate(houses) if h["PhoneModel"] == "google pixel 6")
    hamster_index = next(i for i, h in enumerate(houses) if h["Pet"] == "hamster")
    if hamster_index <= google_pixel_index:
        return False
    
    # 12. The person who is super tall has fish.
    super_tall_index = next(i for i, h in enumerate(houses) if h["Height"] == "super tall")
    if houses[super_tall_index]["Pet"] != "fish":
        return False
    
    # 13. The person with fish is Alice.
    alice_index = next(i for i, h in enumerate(houses) if h["Name"] == "Alice")
    if houses[alice_index]["Pet"] != "fish":
        return False
    
    # 14. The tea drinker is directly left of the person who is a pizza lover.
    for i in range(5):
        if houses[i]["Drink"] == "tea" and houses[i+1]["Food"] == "pizza":
            break
    else:
        return False
    
    # 15. The person who uses a Samsung Galaxy S21 is Carol.
    carol_index = next(i for i, h in enumerate(houses) if h["Name"] == "Carol")
    if houses[carol_index]["PhoneModel"] != "samsung galaxy s21":
        return False
    
    # 16. The person who is a pizza lover is the person who is short.
    pizza_index = next(i for i, h in enumerate(houses) if h["Food"] == "pizza")
    if houses[pizza_index]["Height"] != "short":
        return False
    
    # 17. Arnold is the person who is very tall.
    if houses[arnold_index]["Height"] != "very tall":
        return False
    
    # 18. The person who loves spaghetti is the person who uses Google Pixel 6.
    spaghetti_index = next(i for i, h in enumerate(houses) if h["Food"] == "spaghetti")
    if houses[spaghetti_index]["PhoneModel"] != "google pixel 6":
        return False
    
    # 19. The boba tea drinker is somewhere to the right of the person who loves the soup.
    soup_index = next(i for i, h in enumerate(houses) if h["Food"] == "soup")
    boba_index = next(i for i, h in enumerate(houses) if h["Drink"] == "boba tea")
    if boba_index <= soup_index:
        return False
    
    # 20. The person with a hamster is not in the fifth house.
    if houses[4]["Pet"] == "hamster":
        return False
    
    # 21. The person who is very tall is not in the second house.
    very_tall_index = next(i for i, h in enumerate(houses) if h["Height"] == "very tall")
    if very_tall_index == 1:
        return False
    
    # 22. The person who is super tall is somewhere to the left of Peter.
    peter_index = next(i for i, h in enumerate(houses) if h["Name"] == "Peter")
    super_tall_index = next(i for i, h in enumerate(houses) if h["Height"] == "super tall")
    if super_tall_index >= peter_index:
        return False
    
    # 23. The person who is very short is the person who loves the spaghetti eater.
    very_short_index = next(i for i, h in enumerate(houses) if h["Height"] == "very short")
    if houses[very_short_index]["Food"] != "spaghetti":
        return False
    
    # 24. The person with a bird is somewhere to the left of the person who loves the spaghetti eater.
    bird_index = next(i for i, h in enumerate(houses) if h["Pet"] == "bird")
    if bird_index >= spaghetti_index:
        return False
    
    # 25. The person with an aquarium of fish is directly left of Eric.
    fish_index = next(i for i, h in enumerate(houses) if h["Pet"] == "fish")
    eric_index = next(i for i, h in enumerate(houses) if h["Name"] == "Eric")
    if fish_index + 1 != eric_index:
        return False
    
    # 26. The person with a dog is the person who likes milk.
    for h in houses:
        if h["Pet"] == "dog" and h["Drink"] != "milk":
            return False
    
    return True

# Generate all possible permutations for each category, applying constraints to reduce the search space
for name_perm in permutations(names):
    for food_perm in permutations(foods):
        for height_perm in permutations(heights):
            for drink_perm in permutations(drinks):
                for pet_perm in permutations(pets):
                    for phone_perm in permutations(phones):
                        # Apply fixed constraints
                        # House 3 phone is iPhone 13
                        if phone_perm[2] != "iphone 13":
                            continue
                        # House 2 food is soup
                        if food_perm[1] != "soup":
                            continue
                        # Carol's phone is samsung galaxy s21
                        carol_index = name_perm.index("Carol")
                        if phone_perm[carol_index] != "samsung galaxy s21":
                            continue
                        # Arnold's phone is oneplus 9
                        arnold_index = name_perm.index("Arnold")
                        if phone_perm[arnold_index] != "oneplus 9":
                            continue
                        # Bob is tall
                        bob_index = name_perm.index("Bob")
                        if height_perm[bob_index] != "tall":
                            continue
                        # Grilled cheese is eaten by Bob
                        if food_perm[bob_index] != "grilled cheese":
                            continue
                        # Arnold is very tall
                        if height_perm[arnold_index] != "very tall":
                            continue
                        # Create houses
                        houses = []
                        for i in range(6):
                            house = {
                                "House": str(i + 1),
                                "Name": name_perm[i],
                                "Food": food_perm[i],
                                "Height": height_perm[i],
                                "Drink": drink_perm[i],
                                "Pet": pet_perm[i],
                                "PhoneModel": phone_perm[i]
                            }
                            houses.append(house)
                        # Check all clues
                        if check_solution(houses):
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
                                    "rows": [
                                        [h["House"], h["Name"], h["Food"], h["Height"], h["Drink"], h["Pet"], h["PhoneModel"]]
                                        for h in houses
                                    ]
                                }
                            }
                            print(json.dumps(solution, indent=2))
                            exit()