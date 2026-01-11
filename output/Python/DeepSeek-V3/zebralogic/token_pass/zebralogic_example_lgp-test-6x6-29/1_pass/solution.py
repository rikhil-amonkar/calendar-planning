import itertools
import json

def solve():
    # Define all possible values for each category
    names = ["Arnold", "Carol", "Peter", "Eric", "Bob", "Alice"]
    styles = ["ranch", "colonial", "modern", "craftsman", "mediterranean", "victorian"]
    foods = ["pizza", "stew", "spaghetti", "grilled cheese", "stir fry", "soup"]
    vacations = ["cultural", "cruise", "mountain", "camping", "city", "beach"]
    heights = ["average", "very tall", "very short", "short", "tall", "super tall"]
    cigars = ["yellow monster", "prince", "dunhill", "pall mall", "blue master", "blends"]
    
    houses = [1, 2, 3, 4, 5, 6]
    
    # Generate all permutations of each category
    all_perms = {
        'name': list(itertools.permutations(names, 6)),
        'style': list(itertools.permutations(styles, 6)),
        'food': list(itertools.permutations(foods, 6)),
        'vacation': list(itertools.permutations(vacations, 6)),
        'height': list(itertools.permutations(heights, 6)),
        'cigar': list(itertools.permutations(cigars, 6))
    }
    
    # Helper function to get index of value in permutation
    def idx(perm, value):
        return perm.index(value) + 1
    
    # Filter based on clues
    # Clue 1: Alice is in the fifth house
    all_perms['name'] = [p for p in all_perms['name'] if p[4] == "Alice"]
    
    # Clue 9: Eric is in the fourth house
    all_perms['name'] = [p for p in all_perms['name'] if p[3] == "Eric"]
    
    # Generate all combinations
    solutions = []
    
    for name_perm in all_perms['name']:
        for style_perm in all_perms['style']:
            # Clue 6: Craftsman-style house is not in the third house
            if style_perm[2] == "craftsman":
                continue
                
            for food_perm in all_perms['food']:
                # Clue 2: stir fry = colonial-style house
                if idx(food_perm, "stir fry") != idx(style_perm, "colonial"):
                    continue
                    
                # Clue 3: Alice loves spaghetti eater (Alice's food is spaghetti)
                if food_perm[idx(name_perm, "Alice") - 1] != "spaghetti":
                    continue
                    
                # Clue 4: Arnold loves stew
                if food_perm[idx(name_perm, "Arnold") - 1] != "stew":
                    continue
                    
                # Clue 7: average height = stir fry
                # We'll check this later with height permutations
                
                for vacation_perm in all_perms['vacation']:
                    # Clue 8: beach = ranch-style home
                    if idx(vacation_perm, "beach") != idx(style_perm, "ranch"):
                        continue
                        
                    # Clue 10: One house between colonial and camping
                    colonial_idx = idx(style_perm, "colonial")
                    camping_idx = idx(vacation_perm, "camping")
                    if abs(colonial_idx - camping_idx) != 2:
                        continue
                        
                    # Clue 11: mountain = Yellow Monster smoker
                    # We'll check this later with cigar permutations
                    
                    # Clue 12: mountain = very tall
                    # We'll check this later with height permutations
                    
                    # Clue 14: spaghetti eater = Victorian house
                    spaghetti_idx = idx(food_perm, "spaghetti")
                    if style_perm[spaghetti_idx - 1] != "victorian":
                        continue
                        
                    # Clue 15: tall = beach vacations
                    # We'll check this later with height permutations
                    
                    # Clue 16: tall is left of Victorian house
                    # We'll check this later with height permutations
                    
                    # Clue 17: stir fry is directly left of Bob
                    stir_fry_idx = idx(food_perm, "stir fry")
                    bob_idx = idx(name_perm, "Bob")
                    if stir_fry_idx + 1 != bob_idx:
                        continue
                        
                    # Clue 18: modern-style house is left of Alice
                    modern_idx = idx(style_perm, "modern")
                    alice_idx = idx(name_perm, "Alice")
                    if modern_idx >= alice_idx:
                        continue
                        
                    # Clue 19: Craftsman is left of short person
                    # We'll check this later with height permutations
                    
                    # Clue 20: stir fry is left of Prince smoker
                    # We'll check this later with cigar permutations
                    
                    # Clue 21: Two houses between grilled cheese and super tall
                    # We'll check this later with height permutations
                    
                    # Clue 22: ranch-style home = Blue Master smoker
                    # We'll check this later with cigar permutations
                    
                    # Clue 23: Blends is directly left of Blue Master
                    # We'll check this later with cigar permutations
                    
                    # Clue 24: cultural tours = pizza lover
                    cultural_idx = idx(vacation_perm, "cultural")
                    if food_perm[cultural_idx - 1] != "pizza":
                        continue
                        
                    # Clue 25: pizza lover is left of cruise lover
                    pizza_idx = idx(food_perm, "pizza")
                    cruise_idx = idx(vacation_perm, "cruise")
                    if pizza_idx >= cruise_idx:
                        continue
                        
                    for height_perm in all_perms['height']:
                        # Clue 5: One house between average height and Peter
                        avg_idx = idx(height_perm, "average")
                        peter_idx = idx(name_perm, "Peter")
                        if abs(avg_idx - peter_idx) != 2:
                            continue
                            
                        # Clue 7: average height = stir fry
                        if avg_idx != stir_fry_idx:
                            continue
                            
                        # Clue 12: mountain = very tall
                        mountain_idx = idx(vacation_perm, "mountain")
                        if height_perm[mountain_idx - 1] != "very tall":
                            continue
                            
                        # Clue 15: tall = beach vacations
                        beach_idx = idx(vacation_perm, "beach")
                        if height_perm[beach_idx - 1] != "tall":
                            continue
                            
                        # Clue 16: tall is left of Victorian house
                        tall_idx = idx(height_perm, "tall")
                        victorian_idx = idx(style_perm, "victorian")
                        if tall_idx >= victorian_idx:
                            continue
                            
                        # Clue 19: Craftsman is left of short person
                        craftsman_idx = idx(style_perm, "craftsman")
                        short_idx = idx(height_perm, "short")
                        if craftsman_idx >= short_idx:
                            continue
                            
                        # Clue 21: Two houses between grilled cheese and super tall
                        grilled_idx = idx(food_perm, "grilled cheese")
                        super_tall_idx = idx(height_perm, "super tall")
                        if abs(grilled_idx - super_tall_idx) != 3:
                            continue
                            
                        for cigar_perm in all_perms['cigar']:
                            # Clue 11: mountain = Yellow Monster
                            if cigar_perm[mountain_idx - 1] != "yellow monster":
                                continue
                                
                            # Clue 13: mountain and Dunhill are next to each other
                            dunhill_idx = idx(cigar_perm, "dunhill")
                            if abs(mountain_idx - dunhill_idx) != 1:
                                continue
                                
                            # Clue 20: stir fry is left of Prince smoker
                            prince_idx = idx(cigar_perm, "prince")
                            if stir_fry_idx >= prince_idx:
                                continue
                                
                            # Clue 22: ranch-style home = Blue Master
                            ranch_idx = idx(style_perm, "ranch")
                            if cigar_perm[ranch_idx - 1] != "blue master":
                                continue
                                
                            # Clue 23: Blends is directly left of Blue Master
                            blends_idx = idx(cigar_perm, "blends")
                            if blends_idx + 1 != ranch_idx:
                                continue
                                
                            # All constraints satisfied, found a solution
                            solution = []
                            for house in range(6):
                                row = [
                                    str(house + 1),
                                    name_perm[house],
                                    style_perm[house],
                                    food_perm[house],
                                    vacation_perm[house],
                                    height_perm[house],
                                    cigar_perm[house]
                                ]
                                solution.append(row)
                            
                            # Verify all categories have unique values
                            # (they should since we used permutations)
                            solutions.append(solution)
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution (should be unique)
    solution = solutions[0]
    
    # Sort by house number (already sorted)
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
            "rows": solution
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve()
    print(json.dumps(solution, indent=2))