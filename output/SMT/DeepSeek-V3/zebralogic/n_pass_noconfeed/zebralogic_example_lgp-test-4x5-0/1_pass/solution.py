from z3 import *
import json

def main():
    # Create solver
    solver = Solver()
    
    # Define houses
    n_houses = 4
    houses = [1, 2, 3, 4]
    
    # Define attributes
    names = ['Eric', 'Peter', 'Arnold', 'Alice']
    smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    cigars = ['blue master', 'pall mall', 'dunhill', 'prince']
    heights = ['tall', 'average', 'short', 'very short']
    phones = ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in houses]
    smoothie_vars = [Int(f'smoothie_{i}') for i in houses]
    cigar_vars = [Int(f'cigar_{i}') for i in houses]
    height_vars = [Int(f'height_{i}') for i in houses]
    phone_vars = [Int(f'phone_{i}') for i in houses]
    
    # Domain constraints - each attribute variable must be in [0, 3]
    for i in houses:
        solver.add(And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(And(smoothie_vars[i-1] >= 0, smoothie_vars[i-1] < len(smoothies)))
        solver.add(And(cigar_vars[i-1] >= 0, cigar_vars[i-1] < len(cigars)))
        solver.add(And(height_vars[i-1] >= 0, height_vars[i-1] < len(heights)))
        solver.add(And(phone_vars[i-1] >= 0, phone_vars[i-1] < len(phones)))
    
    # All attributes must have distinct values per house
    solver.add(Distinct(name_vars))
    solver.add(Distinct(smoothie_vars))
    solver.add(Distinct(cigar_vars))
    solver.add(Distinct(height_vars))
    solver.add(Distinct(phone_vars))
    
    # Clue 1: The Dragonfruit smoothie lover is Eric.
    dragonfruit_idx = smoothies.index('dragonfruit')
    eric_idx = names.index('Eric')
    for i in houses:
        solver.add(Implies(smoothie_vars[i-1] == dragonfruit_idx, name_vars[i-1] == eric_idx))
    
    # Clue 2: The Dunhill smoker is the person who likes Cherry smoothies.
    dunhill_idx = cigars.index('dunhill')
    cherry_idx = smoothies.index('cherry')
    for i in houses:
        solver.add(Implies(cigar_vars[i-1] == dunhill_idx, smoothie_vars[i-1] == cherry_idx))
    
    # Clue 3: The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    samsung_idx = phones.index('samsung galaxy s21')
    iphone_idx = phones.index('iphone 13')
    for i in range(1, n_houses):
        solver.add(Implies(phone_vars[i-1] == samsung_idx, phone_vars[i] == iphone_idx))
    
    # Clue 4: The Dunhill smoker is somewhere to the right of the person who is very short.
    very_short_idx = heights.index('very short')
    for i in houses:
        for j in range(1, i):  # j < i (right means higher house number)
            solver.add(Implies(cigar_vars[i-1] == dunhill_idx, height_vars[j-1] == very_short_idx))
    
    # Clue 5: The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
    watermelon_idx = smoothies.index('watermelon')
    desert_idx = smoothies.index('desert')
    for i in houses:
        for j in range(1, i):  # j < i (right means higher house number)
            solver.add(Implies(smoothie_vars[i-1] == watermelon_idx, smoothie_vars[j-1] == desert_idx))
    
    # Clue 6: The Prince smoker is the person who uses a OnePlus 9.
    prince_idx = cigars.index('prince')
    oneplus_idx = phones.index('oneplus 9')
    for i in houses:
        solver.add(Implies(cigar_vars[i-1] == prince_idx, phone_vars[i-1] == oneplus_idx))
    
    # Clue 7: The person who is tall is in the third house.
    tall_idx = heights.index('tall')
    solver.add(height_vars[2] == tall_idx)
    
    # Clue 8: The person who is very short is the person who uses an iPhone 13.
    for i in houses:
        solver.add(Implies(height_vars[i-1] == very_short_idx, phone_vars[i-1] == iphone_idx))
    
    # Clue 9: The person who smokes Blue Master is not in the first house.
    blue_master_idx = cigars.index('blue master')
    solver.add(cigar_vars[0] != blue_master_idx)
    
    # Clue 10: The Dunhill smoker is the person who is short.
    short_idx = heights.index('short')
    for i in houses:
        solver.add(Implies(cigar_vars[i-1] == dunhill_idx, height_vars[i-1] == short_idx))
    
    # Clue 11: Peter is not in the third house.
    peter_idx = names.index('Peter')
    solver.add(name_vars[2] != peter_idx)
    
    # Clue 12: Arnold is the person who uses a Google Pixel 6.
    arnold_idx = names.index('Arnold')
    google_pixel_idx = phones.index('google pixel 6')
    for i in houses:
        solver.add(Implies(name_vars[i-1] == arnold_idx, phone_vars[i-1] == google_pixel_idx))
    
    # Clue 13: The Dragonfruit smoothie lover is the person partial to Pall Mall.
    pall_mall_idx = cigars.index('pall mall')
    for i in houses:
        solver.add(Implies(smoothie_vars[i-1] == dragonfruit_idx, cigar_vars[i-1] == pall_mall_idx))
    
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
        for i in houses:
            name_val = model.evaluate(name_vars[i-1])
            smoothie_val = model.evaluate(smoothie_vars[i-1])
            cigar_val = model.evaluate(cigar_vars[i-1])
            height_val = model.evaluate(height_vars[i-1])
            phone_val = model.evaluate(phone_vars[i-1])
            
            row = [
                str(i),
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