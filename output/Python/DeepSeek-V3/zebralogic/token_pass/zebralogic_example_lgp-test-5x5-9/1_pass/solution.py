import json
from itertools import permutations

def solve():
    # Define all possible values
    names = ["Bob", "Arnold", "Peter", "Alice", "Eric"]
    drinks = ["milk", "root beer", "coffee", "tea", "water"]
    colors = ["blue", "green", "white", "yellow", "red"]
    flowers = ["daffodils", "roses", "lilies", "tulips", "carnations"]
    hobbies = ["painting", "cooking", "photography", "gardening", "knitting"]
    
    houses = [1, 2, 3, 4, 5]
    
    # Generate all permutations for each category
    for name_perm in permutations(names, 5):
        # Clue 1: Alice is not in the fourth house
        if name_perm[3] == "Alice":
            continue
            
        # Clue 8 & 13: Peter drinks water and is in house 3
        if name_perm[2] != "Peter":
            continue
            
        # Clue 9: Arnold is the photography enthusiast
        # We'll check this later when we have hobbies
        
        for drink_perm in permutations(drinks, 5):
            # Clue 13: Water drinker is in house 3
            if drink_perm[2] != "water":
                continue
                
            # Clue 8: Peter drinks water (already enforced by position)
            # Verify Peter's drink matches
            if name_perm[2] == "Peter" and drink_perm[2] != "water":
                continue
                
            # Clue 7: Eric is directly left of the tea drinker
            try:
                eric_index = name_perm.index("Eric")
                if eric_index == 4 or drink_perm[eric_index + 1] != "tea":
                    continue
            except:
                continue
                
            for color_perm in permutations(colors, 5):
                # Clue 15: White is in house 2
                if color_perm[1] != "white":
                    continue
                    
                # Clue 3 & 4: Green color = coffee drinker AND lilies lover
                # We'll check coffee later, lilies when we have flowers
                
                # Clue 5: Blue is somewhere to the right of daffodils
                # We'll check when we have flowers
                
                # Clue 6: Blue color = cooking hobby
                # We'll check when we have hobbies
                
                # Clue 10: White color = roses lover
                # We'll check when we have flowers
                
                # Clue 11: One house between carnations and red color
                # We'll check when we have flowers
                
                for flower_perm in permutations(flowers, 5):
                    # Clue 4: Green color = lilies lover
                    for i in range(5):
                        if color_perm[i] == "green" and flower_perm[i] != "lilies":
                            break
                        if flower_perm[i] == "lilies" and color_perm[i] != "green":
                            break
                    else:
                        # Clue 10: White color = roses lover
                        if flower_perm[1] != "roses":  # white is in house 2
                            continue
                            
                        # Clue 5: Blue is somewhere to the right of daffodils
                        blue_index = color_perm.index("blue") if "blue" in color_perm else -1
                        daffodils_index = flower_perm.index("daffodils") if "daffodils" in flower_perm else -1
                        if blue_index <= daffodils_index:
                            continue
                            
                        # Clue 11: One house between carnations and red color
                        carnations_index = flower_perm.index("carnations") if "carnations" in flower_perm else -1
                        red_index = color_perm.index("red") if "red" in color_perm else -1
                        if abs(carnations_index - red_index) != 2:
                            continue
                            
                        # Clue 14: Carnations lover = root beer drinker
                        if carnations_index != -1 and drink_perm[carnations_index] != "root beer":
                            continue
                            
                        for hobby_perm in permutations(hobbies, 5):
                            # Clue 2: Root beer lover = gardening hobby
                            for i in range(5):
                                if drink_perm[i] == "root beer" and hobby_perm[i] != "gardening":
                                    break
                                if hobby_perm[i] == "gardening" and drink_perm[i] != "root beer":
                                    break
                            else:
                                # Clue 3: Green color = coffee drinker
                                for i in range(5):
                                    if color_perm[i] == "green" and drink_perm[i] != "coffee":
                                        break
                                    if drink_perm[i] == "coffee" and color_perm[i] != "green":
                                        break
                                else:
                                    # Clue 6: Blue color = cooking hobby
                                    for i in range(5):
                                        if color_perm[i] == "blue" and hobby_perm[i] != "cooking":
                                            break
                                        if hobby_perm[i] == "cooking" and color_perm[i] != "blue":
                                            break
                                    else:
                                        # Clue 9: Arnold = photography
                                        arnold_index = name_perm.index("Arnold")
                                        if hobby_perm[arnold_index] != "photography":
                                            continue
                                            
                                        # Clue 12: Cooking is somewhere to the left of painting
                                        cooking_index = hobby_perm.index("cooking")
                                        painting_index = hobby_perm.index("painting")
                                        if cooking_index >= painting_index:
                                            continue
                                            
                                        # All constraints satisfied!
                                        # Build the solution
                                        solution = {
                                            "solution": {
                                                "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
                                                "rows": []
                                            }
                                        }
                                        
                                        for i in range(5):
                                            row = [
                                                str(i + 1),
                                                name_perm[i],
                                                drink_perm[i],
                                                color_perm[i],
                                                flower_perm[i],
                                                hobby_perm[i]
                                            ]
                                            solution["solution"]["rows"].append(row)
                                        
                                        return solution

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))