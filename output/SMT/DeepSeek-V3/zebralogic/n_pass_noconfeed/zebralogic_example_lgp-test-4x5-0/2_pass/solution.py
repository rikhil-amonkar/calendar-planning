from z3 import *
import json

def main():
    # Create solver
    solver = Solver()
    
    # Define houses
    n_houses = 4
    houses = [0, 1, 2, 3]  # Using 0-indexing for easier array access
    
    # Define attributes
    names = ['Eric', 'Peter', 'Arnold', 'Alice']
    smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    cigars = ['blue master', 'pall mall', 'dunhill', 'prince']
    heights = ['tall', 'average', 'short', 'very short']
    phones = ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in range(n_houses)]
    smoothie_vars = [Int(f'smoothie_{i}') for i in range(n_houses)]
    cigar_vars = [Int(f'cigar_{i}') for i in range(n_houses)]
    height_vars = [Int(f'height_{i}') for i in range(n_houses)]
    phone_vars = [Int(f'phone_{i}') for i in range(n_houses)]
    
    # Domain constraints - each attribute variable must be in [0, 3]
    for i in range(n_houses):
        solver.add(And(name_vars[i] >= 0, name_vars[i] < len(names)))
        solver.add(And(smoothie_vars[i] >= 0, smoothie_vars[i] < len(smoothies)))
        solver.add(And(cigar_vars[i] >= 0, cigar_vars[i] < len(cigars)))
        solver.add(And(height_vars[i] >= 0, height_vars[i] < len(heights)))
        solver.add(And(phone_vars[i] >= 0, phone_vars[i] < len(phones)))
    
    # All attributes must have distinct values per house
    solver.add(Distinct(name_vars))
    solver.add(Distinct(smoothie_vars))
    solver.add(Distinct(cigar_vars))
    solver.add(Distinct(height_vars))
    solver.add(Distinct(phone_vars))
    
    # Get indices for easier reference
    eric_idx = names.index('Eric')
    peter_idx = names.index('Peter')
    arnold_idx = names.index('Arnold')
    alice_idx = names.index('Alice')
    
    dragonfruit_idx = smoothies.index('dragonfruit')
    cherry_idx = smoothies.index('cherry')
    desert_idx = smoothies.index('desert')
    watermelon_idx = smoothies.index('watermelon')
    
    blue_master_idx = cigars.index('blue master')
    pall_mall_idx = cigars.index('pall mall')
    dunhill_idx = cigars.index('dunhill')
    prince_idx = cigars.index('prince')
    
    tall_idx = heights.index('tall')
    average_idx = heights.index('average')
    short_idx = heights.index('short')
    very_short_idx = heights.index('very short')
    
    google_pixel_idx = phones.index('google pixel 6')
    samsung_idx = phones.index('samsung galaxy s21')
    iphone_idx = phones.index('iphone 13')
    oneplus_idx = phones.index('oneplus 9')
    
    # Clue 1: The Dragonfruit smoothie lover is Eric.
    for i in range(n_houses):
        solver.add(Implies(smoothie_vars[i] == dragonfruit_idx, name_vars[i] == eric_idx))
    
    # Clue 2: The Dunhill smoker is the person who likes Cherry smoothies.
    for i in range(n_houses):
        solver.add(Implies(cigar_vars[i] == dunhill_idx, smoothie_vars[i] == cherry_idx))
    
    # Clue 3: The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    for i in range(n_houses - 1):
        solver.add(Implies(phone_vars[i] == samsung_idx, phone_vars[i + 1] == iphone_idx))
    
    # Clue 4: The Dunhill smoker is somewhere to the right of the person who is very short.
    # Create variables to track positions
    dunhill_pos = Int('dunhill_pos')
    very_short_pos = Int('very_short_pos')
    solver.add(dunhill_pos >= 0, dunhill_pos < n_houses)
    solver.add(very_short_pos >= 0, very_short_pos < n_houses)
    
    for i in range(n_houses):
        solver.add(Implies(cigar_vars[i] == dunhill_idx, dunhill_pos == i))
        solver.add(Implies(height_vars[i] == very_short_idx, very_short_pos == i))
    
    solver.add(dunhill_pos > very_short_pos)
    
    # Clue 5: The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
    watermelon_pos = Int('watermelon_pos')
    desert_pos = Int('desert_pos')
    solver.add(watermelon_pos >= 0, watermelon_pos < n_houses)
    solver.add(desert_pos >= 0, desert_pos < n_houses)
    
    for i in range(n_houses):
        solver.add(Implies(smoothie_vars[i] == watermelon_idx, watermelon_pos == i))
        solver.add(Implies(smoothie_vars[i] == desert_idx, desert_pos == i))
    
    solver.add(watermelon_pos > desert_pos)
    
    # Clue 6: The Prince smoker is the person who uses a OnePlus 9.
    for i in range(n_houses):
        solver.add(Implies(cigar_vars[i] == prince_idx, phone_vars[i] == oneplus_idx))
    
    # Clue 7: The person who is tall is in the third house.
    solver.add(height_vars[2] == tall_idx)
    
    # Clue 8: The person who is very short is the person who uses an iPhone 13.
    for i in range(n_houses):
        solver.add(Implies(height_vars[i] == very_short_idx, phone_vars[i] == iphone_idx))
    
    # Clue 9: The person who smokes Blue Master is not in the first house.
    solver.add(cigar_vars[0] != blue_master_idx)
    
    # Clue 10: The Dunhill smoker is the person who is short.
    for i in range(n_houses):
        solver.add(Implies(cigar_vars[i] == dunhill_idx, height_vars[i] == short_idx))
    
    # Clue 11: Peter is not in the third house.
    solver.add(name_vars[2] != peter_idx)
    
    # Clue 12: Arnold is the person who uses a Google Pixel 6.
    for i in range(n_houses):
        solver.add(Implies(name_vars[i] == arnold_idx, phone_vars[i] == google_pixel_idx))
    
    # Clue 13: The Dragonfruit smoothie lover is the person partial to Pall Mall.
    for i in range(n_houses):
        solver.add(Implies(smoothie_vars[i] == dragonfruit_idx, cigar_vars[i] == pall_mall_idx))
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare solution data
        solution_data = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for i in range(n_houses):
            name_val = model.evaluate(name_vars[i])
            smoothie_val = model.evaluate(smoothie_vars[i])
            cigar_val = model.evaluate(cigar_vars[i])
            height_val = model.evaluate(height_vars[i])
            phone_val = model.evaluate(phone_vars[i])
            
            row = [
                str(i + 1),
                names[name_val.as_long()],
                smoothies[smoothie_val.as_long()],
                cigars[cigar_val.as_long()],
                heights[height_val.as_long()],
                phones[phone_val.as_long()]
            ]
            solution_data["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(solution_data, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()