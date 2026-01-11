import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ["Peter", "Carol", "Eric", "Alice", "Bob", "Arnold"]
    phones = ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"]
    cigars = ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"]
    flowers = ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"]
    colors = ["yellow", "red", "green", "blue", "white", "purple"]
    sports = ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"]
    
    houses = [1, 2, 3, 4, 5, 6]
    
    # Try all permutations for each category
    for name_perm in permutations(names, 6):
        # Constraint 18: Alice is in the first house
        if name_perm[0] != "Alice":
            continue
            
        for phone_perm in permutations(phones, 6):
            # Constraint 1: OnePlus 9 is in the second house
            if phone_perm[1] != "oneplus 9":
                continue
                
            for cigar_perm in permutations(cigars, 6):
                for flower_perm in permutations(flowers, 6):
                    # Constraint 17: Tulips is Bob
                    bob_index = name_perm.index("Bob")
                    if flower_perm[bob_index] != "tulips":
                        continue
                    
                    # Constraint 3: Carol loves carnations
                    carol_index = name_perm.index("Carol")
                    if flower_perm[carol_index] != "carnations":
                        continue
                    
                    # Constraint 8: Two houses between Carol and daffodils
                    daffodils_index = flower_perm.index("daffodils")
                    if abs(carol_index - daffodils_index) != 3:
                        continue
                    
                    for color_perm in permutations(colors, 6):
                        # Constraint 6: Yellow and blue are next to each other
                        yellow_index = color_perm.index("yellow")
                        blue_index = color_perm.index("blue")
                        if abs(yellow_index - blue_index) != 1:
                            continue
                        
                        # Constraint 16: Blue is Peter
                        peter_index = name_perm.index("Peter")
                        if color_perm[peter_index] != "blue":
                            continue
                        
                        # Constraint 4: Purple is directly left of Pall Mall
                        purple_index = color_perm.index("purple")
                        pall_mall_index = cigar_perm.index("pall mall")
                        if purple_index + 1 != pall_mall_index:
                            continue
                        
                        for sport_perm in permutations(sports, 6):
                            # Constraint 21: Soccer is Carol
                            if sport_perm[carol_index] != "soccer":
                                continue
                            
                            # Constraint 9: Prince smoker loves basketball
                            prince_index = cigar_perm.index("prince")
                            if sport_perm[prince_index] != "basketball":
                                continue
                            
                            # Constraint 10: Dunhill smoker loves volleyball
                            dunhill_index = cigar_perm.index("dunhill")
                            if sport_perm[dunhill_index] != "volleyball":
                                continue
                            
                            # Constraint 11: Swimming person uses Google Pixel 6
                            swimming_index = sport_perm.index("swimming")
                            if phone_perm[swimming_index] != "google pixel 6":
                                continue
                            
                            # Constraint 15: Dunhill smoker is Peter
                            if name_perm[dunhill_index] != "Peter":
                                continue
                            
                            # Constraint 5: Green color person smokes Blue Master
                            green_index = color_perm.index("green")
                            blue_master_index = cigar_perm.index("blue master")
                            if green_index != blue_master_index:
                                continue
                            
                            # Constraint 19: Baseball is directly left of Blue Master smoker
                            baseball_index = sport_perm.index("baseball")
                            if baseball_index + 1 != blue_master_index:
                                continue
                            
                            # Constraint 24: Volleyball person uses iPhone 13
                            volleyball_index = sport_perm.index("volleyball")
                            if phone_perm[volleyball_index] != "iphone 13":
                                continue
                            
                            # Constraint 7: Eric is somewhere to the right of Samsung Galaxy S21 user
                            eric_index = name_perm.index("Eric")
                            samsung_index = phone_perm.index("samsung galaxy s21")
                            if eric_index <= samsung_index:
                                continue
                            
                            # Constraint 14: Iris is somewhere to the left of Eric
                            iris_index = flower_perm.index("iris")
                            if iris_index >= eric_index:
                                continue
                            
                            # Constraint 23: Eric smokes blends
                            if cigar_perm[eric_index] != "blends":
                                continue
                            
                            # Constraint 22: Carnations is directly left of blends smoker
                            if carol_index + 1 != eric_index:
                                continue
                            
                            # Constraint 20: Google Pixel 6 is somewhere to the right of blends smoker
                            google_pixel_index = phone_perm.index("google pixel 6")
                            if google_pixel_index <= eric_index:
                                continue
                            
                            # Constraint 2: Xiaomi Mi 11 is somewhere to the left of Huawei P50
                            xiaomi_index = phone_perm.index("xiaomi mi 11")
                            huawei_index = phone_perm.index("huawei p50")
                            if xiaomi_index >= huawei_index:
                                continue
                            
                            # Constraint 12: Huawei P50 is directly left of white color
                            white_index = color_perm.index("white")
                            if huawei_index + 1 != white_index:
                                continue
                            
                            # Constraint 13: OnePlus 9 and roses are next to each other
                            roses_index = flower_perm.index("roses")
                            if abs(1 - roses_index) != 1:  # OnePlus 9 is at house 2 (index 1)
                                continue
                            
                            # All constraints satisfied! Create solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
                                    "rows": []
                                }
                            }
                            
                            for i in range(6):
                                row = [
                                    str(i + 1),
                                    name_perm[i],
                                    phone_perm[i],
                                    cigar_perm[i],
                                    flower_perm[i],
                                    color_perm[i],
                                    sport_perm[i]
                                ]
                                solution["solution"]["rows"].append(row)
                            
                            return solution
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()