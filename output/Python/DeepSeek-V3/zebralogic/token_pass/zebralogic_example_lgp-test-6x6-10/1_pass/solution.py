import json
from itertools import permutations

def solve():
    houses = [1, 2, 3, 4, 5, 6]
    
    # All possible values for each category
    names = ["Arnold", "Bob", "Peter", "Alice", "Carol", "Eric"]
    foods = ["stew", "grilled cheese", "stir fry", "soup", "pizza", "spaghetti"]
    heights = ["tall", "average", "super tall", "very short", "very tall", "short"]
    drinks = ["root beer", "boba tea", "coffee", "water", "tea", "milk"]
    pets = ["hamster", "fish", "cat", "dog", "bird", "rabbit"]
    phones = ["samsung galaxy s21", "xiaomi mi 11", "google pixel 6", 
              "iphone 13", "huawei p50", "oneplus 9"]
    
    # Try all permutations (brute force with pruning)
    solutions = []
    
    # We'll iterate over all possible assignments
    # Since 6!^6 is huge, we'll use backtracking with constraints
    
    # Helper to check if assignment is consistent
    def check_constraints(assignment):
        # assignment is dict: house -> (name, food, height, drink, pet, phone)
        
        # Build maps for quick lookup
        pos = {}
        name_to_house = {}
        food_to_house = {}
        height_to_house = {}
        drink_to_house = {}
        pet_to_house = {}
        phone_to_house = {}
        
        for h in houses:
            if h not in assignment:
                continue
            n, f, ht, d, p, ph = assignment[h]
            pos[h] = (n, f, ht, d, p, ph)
            name_to_house[n] = h
            food_to_house[f] = h
            height_to_house[ht] = h
            drink_to_house[d] = h
            pet_to_house[p] = h
            phone_to_house[ph] = h
        
        # 1. iPhone 13 in third house
        if 3 in pos and pos[3][5] != "iphone 13":
            return False
        if "iphone 13" in phone_to_house and phone_to_house["iphone 13"] != 3:
            return False
        
        # 2. Bob is tall
        if "Bob" in name_to_house and "tall" in height_to_house:
            if name_to_house["Bob"] != height_to_house["tall"]:
                return False
        
        # 3. Soup in second house
        if 2 in pos and pos[2][1] != "soup":
            return False
        if "soup" in food_to_house and food_to_house["soup"] != 2:
            return False
        
        # 4. root beer directly left of Xiaomi Mi 11
        if "root beer" in drink_to_house and "xiaomi mi 11" in phone_to_house:
            if drink_to_house["root beer"] + 1 != phone_to_house["xiaomi mi 11"]:
                return False
        
        # 5. Huawei P50 directly left of grilled cheese
        if "huawei p50" in phone_to_house and "grilled cheese" in food_to_house:
            if phone_to_house["huawei p50"] + 1 != food_to_house["grilled cheese"]:
                return False
        
        # 6. stir fry person likes milk
        if "stir fry" in food_to_house and "milk" in drink_to_house:
            if food_to_house["stir fry"] != drink_to_house["milk"]:
                return False
        
        # 7. grilled cheese person is tall
        if "grilled cheese" in food_to_house and "tall" in height_to_house:
            if food_to_house["grilled cheese"] != height_to_house["tall"]:
                return False
        
        # 8. Xiaomi Mi 11 is coffee drinker
        if "xiaomi mi 11" in phone_to_house and "coffee" in drink_to_house:
            if phone_to_house["xiaomi mi 11"] != drink_to_house["coffee"]:
                return False
        
        # 9. OnePlus 9 is Arnold
        if "oneplus 9" in phone_to_house and "Arnold" in name_to_house:
            if phone_to_house["oneplus 9"] != name_to_house["Arnold"]:
                return False
        
        # 10. Rabbit not in fifth house
        if "rabbit" in pet_to_house and pet_to_house["rabbit"] == 5:
            return False
        
        # 11. Hamster somewhere to the right of Google Pixel 6
        if "hamster" in pet_to_house and "google pixel 6" in phone_to_house:
            if pet_to_house["hamster"] <= phone_to_house["google pixel 6"]:
                return False
        
        # 12. Super tall person has fish
        if "super tall" in height_to_house and "fish" in pet_to_house:
            if height_to_house["super tall"] != pet_to_house["fish"]:
                return False
        
        # 13. Fish is Alice
        if "fish" in pet_to_house and "Alice" in name_to_house:
            if pet_to_house["fish"] != name_to_house["Alice"]:
                return False
        
        # 14. Tea drinker directly left of pizza lover
        if "tea" in drink_to_house and "pizza" in food_to_house:
            if drink_to_house["tea"] + 1 != food_to_house["pizza"]:
                return False
        
        # 15. Samsung Galaxy S21 is Carol
        if "samsung galaxy s21" in phone_to_house and "Carol" in name_to_house:
            if phone_to_house["samsung galaxy s21"] != name_to_house["Carol"]:
                return False
        
        # 16. Pizza lover is short
        if "pizza" in food_to_house and "short" in height_to_house:
            if food_to_house["pizza"] != height_to_house["short"]:
                return False
        
        # 17. Arnold is very tall
        if "Arnold" in name_to_house and "very tall" in height_to_house:
            if name_to_house["Arnold"] != height_to_house["very tall"]:
                return False
        
        # 18. Spaghetti eater uses Google Pixel 6
        if "spaghetti" in food_to_house and "google pixel 6" in phone_to_house:
            if food_to_house["spaghetti"] != phone_to_house["google pixel 6"]:
                return False
        
        # 19. Boba tea drinker somewhere to the right of soup lover (soup in house 2)
        if "boba tea" in drink_to_house:
            if drink_to_house["boba tea"] <= 2:
                return False
        
        # 20. Hamster not in fifth house (same as 10 but for hamster)
        if "hamster" in pet_to_house and pet_to_house["hamster"] == 5:
            return False
        
        # 21. Very tall not in second house
        if "very tall" in height_to_house and height_to_house["very tall"] == 2:
            return False
        
        # 22. Super tall is somewhere to the left of Peter
        if "super tall" in height_to_house and "Peter" in name_to_house:
            if height_to_house["super tall"] >= name_to_house["Peter"]:
                return False
        
        # 23. Very short is spaghetti eater
        if "very short" in height_to_house and "spaghetti" in food_to_house:
            if height_to_house["very short"] != food_to_house["spaghetti"]:
                return False
        
        # 24. Bird is somewhere to the left of spaghetti eater
        if "bird" in pet_to_house and "spaghetti" in food_to_house:
            if pet_to_house["bird"] >= food_to_house["spaghetti"]:
                return False
        
        # 25. Fish is directly left of Eric
        if "fish" in pet_to_house and "Eric" in name_to_house:
            if pet_to_house["fish"] + 1 != name_to_house["Eric"]:
                return False
        
        # 26. Dog owner likes milk
        if "dog" in pet_to_house and "milk" in drink_to_house:
            if pet_to_house["dog"] != drink_to_house["milk"]:
                return False
        
        return True
    
    # Backtracking search
    def backtrack(house_idx, assignments, used_names, used_foods, used_heights, 
                  used_drinks, used_pets, used_phones):
        if house_idx > 6:
            if check_constraints(assignments):
                solutions.append(assignments.copy())
            return
        
        # Try all combinations for this house
        for name in names:
            if name in used_names:
                continue
            for food in foods:
                if food in used_foods:
                    continue
                for height in heights:
                    if height in used_heights:
                        continue
                    for drink in drinks:
                        if drink in used_drinks:
                            continue
                        for pet in pets:
                            if pet in used_pets:
                                continue
                            for phone in phones:
                                if phone in used_phones:
                                    continue
                                
                                # Assign
                                assignments[house_idx] = (name, food, height, drink, pet, phone)
                                used_names.add(name)
                                used_foods.add(food)
                                used_heights.add(height)
                                used_drinks.add(drink)
                                used_pets.add(pet)
                                used_phones.add(phone)
                                
                                # Check partial constraints that involve this house
                                if check_constraints(assignments):
                                    backtrack(house_idx + 1, assignments, used_names, 
                                             used_foods, used_heights, used_drinks, 
                                             used_pets, used_phones)
                                
                                # Backtrack
                                del assignments[house_idx]
                                used_names.remove(name)
                                used_foods.remove(food)
                                used_heights.remove(height)
                                used_drinks.remove(drink)
                                used_pets.remove(pet)
                                used_phones.remove(phone)
    
    # Start search
    backtrack(1, {}, set(), set(), set(), set(), set(), set())
    
    if not solutions:
        return None
    
    # Take first solution
    sol = solutions[0]
    
    # Build output
    header = ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"]
    rows = []
    for h in sorted(sol.keys()):
        name, food, height, drink, pet, phone = sol[h]
        rows.append([str(h), name, food, height, drink, pet, phone])
    
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve()
    print(json.dumps(solution, indent=2))