import json
from itertools import permutations

def main():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Arnold', 'Carol', 'Peter', 'Eric', 'Bob', 'Alice']
    styles = ['ranch', 'colonial', 'modern', 'craftsman', 'mediterranean', 'victorian']
    foods = ['pizza', 'stew', 'spaghetti', 'grilled cheese', 'stir fry', 'soup']
    vacations = ['cultural', 'cruise', 'mountain', 'camping', 'city', 'beach']
    heights = ['average', 'very tall', 'very short', 'short', 'tall', 'super tall']
    cigars = ['yellow monster', 'prince', 'dunhill', 'pall mall', 'blue master', 'blends']

    # Pre-define known positions
    alice_pos = 5  # Clue 1
    eric_pos = 4   # Clue 9

    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        if name_perm[alice_pos-1] != 'Alice': continue
        if name_perm[eric_pos-1] != 'Eric': continue
        
        for style_perm in permutations(styles):
            # Clue 2: stir fry eater lives in colonial
            # Clue 7: average height loves stir fry
            # So average height = stir fry = colonial
            
            # Clue 6: craftsman not in third
            if style_perm[2] == 'craftsman': continue
            
            for food_perm in permutations(foods):
                # Clue 2: stir fry = colonial style
                colonial_pos = style_perm.index('colonial') + 1
                if food_perm[colonial_pos-1] != 'stir fry': continue
                
                # Clue 3: Alice loves spaghetti eater (Alice is spaghetti eater)
                if food_perm[alice_pos-1] != 'spaghetti': continue
                
                # Clue 4: Arnold loves stew
                arnold_pos = name_perm.index('Arnold') + 1
                if food_perm[arnold_pos-1] != 'stew': continue
                
                # Clue 17: stir fry directly left of Bob
                stir_fry_pos = food_perm.index('stir fry') + 1
                bob_pos = name_perm.index('Bob') + 1
                if stir_fry_pos + 1 != bob_pos: continue
                
                for vacation_perm in permutations(vacations):
                    # Clue 8: beach vacation = ranch style
                    ranch_pos = style_perm.index('ranch') + 1
                    if vacation_perm[ranch_pos-1] != 'beach': continue
                    
                    # Clue 10: one house between colonial and camping
                    camping_pos = vacation_perm.index('camping') + 1
                    if abs(colonial_pos - camping_pos) != 2: continue
                    
                    # Clue 11: mountain retreats = yellow monster cigar
                    # Clue 12: mountain retreats = very tall height
                    # So mountain = yellow monster = very tall
                    
                    # Clue 24: cultural tours = pizza lover
                    cultural_pos = vacation_perm.index('cultural') + 1
                    pizza_pos = food_perm.index('pizza') + 1
                    if cultural_pos != pizza_pos: continue
                    
                    # Clue 25: pizza lover left of cruise lover
                    cruise_pos = vacation_perm.index('cruise') + 1
                    if pizza_pos >= cruise_pos: continue
                    
                    for height_perm in permutations(heights):
                        # Clue 5: one house between average height and Peter
                        average_pos = height_perm.index('average') + 1
                        peter_pos = name_perm.index('Peter') + 1
                        if abs(average_pos - peter_pos) != 2: continue
                        
                        # Clue 7: average height = stir fry
                        if average_pos != stir_fry_pos: continue
                        
                        # Clue 12: mountain retreats = very tall
                        mountain_pos = vacation_perm.index('mountain') + 1
                        very_tall_pos = height_perm.index('very tall') + 1
                        if mountain_pos != very_tall_pos: continue
                        
                        # Clue 15: tall = beach vacations
                        tall_pos = height_perm.index('tall') + 1
                        if tall_pos != ranch_pos: continue
                        
                        # Clue 16: tall left of victorian house
                        victorian_pos = style_perm.index('victorian') + 1
                        if tall_pos >= victorian_pos: continue
                        
                        # Clue 19: craftsman left of short
                        craftsman_pos = style_perm.index('craftsman') + 1
                        short_pos = height_perm.index('short') + 1
                        if craftsman_pos >= short_pos: continue
                        
                        # Clue 21: two houses between grilled cheese and super tall
                        grilled_cheese_pos = food_perm.index('grilled cheese') + 1
                        super_tall_pos = height_perm.index('super tall') + 1
                        if abs(grilled_cheese_pos - super_tall_pos) != 3: continue
                        
                        for cigar_perm in permutations(cigars):
                            # Clue 11: mountain retreats = yellow monster
                            yellow_monster_pos = cigar_perm.index('yellow monster') + 1
                            if yellow_monster_pos != mountain_pos: continue
                            
                            # Clue 13: mountain and dunhill adjacent
                            dunhill_pos = cigar_perm.index('dunhill') + 1
                            if abs(mountain_pos - dunhill_pos) != 1: continue
                            
                            # Clue 20: stir fry left of prince smoker
                            prince_pos = cigar_perm.index('prince') + 1
                            if stir_fry_pos >= prince_pos: continue
                            
                            # Clue 22: ranch style = blue master
                            blue_master_pos = cigar_perm.index('blue master') + 1
                            if blue_master_pos != ranch_pos: continue
                            
                            # Clue 23: blends directly left of blue master
                            blends_pos = cigar_perm.index('blends') + 1
                            if blends_pos + 1 != blue_master_pos: continue
                            
                            # Clue 14: spaghetti eater = victorian house (already handled by clue 3 and clue 14)
                            # Alice is spaghetti eater and clue 14 says spaghetti eater = victorian house
                            if victorian_pos != alice_pos: continue
                            
                            # Clue 18: modern left of Alice
                            modern_pos = style_perm.index('modern') + 1
                            if modern_pos >= alice_pos: continue
                            
                            # All constraints satisfied, found solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
                                    "rows": []
                                }
                            }
                            
                            for i in range(6):
                                row = [
                                    str(i+1),
                                    name_perm[i],
                                    style_perm[i],
                                    food_perm[i],
                                    vacation_perm[i],
                                    height_perm[i],
                                    cigar_perm[i]
                                ]
                                solution["solution"]["rows"].append(row)
                            
                            print(json.dumps(solution, indent=2))
                            return
    
    print('{"solution": {"header": [], "rows": []}}')

if __name__ == "__main__":
    main()