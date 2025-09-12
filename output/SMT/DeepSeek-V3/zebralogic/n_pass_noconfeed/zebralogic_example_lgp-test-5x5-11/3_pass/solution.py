from z3 import *
import json

def main():
    solver = Solver()
    
    n = 5
    houses = [1, 2, 3, 4, 5]
    
    # Define variables for each attribute
    names = ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice']
    name_vars = [Int(f'name_{i}') for i in houses]
    for i in houses:
        solver.add(And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
    solver.add(Distinct(name_vars))
    
    heights = ['average', 'very tall', 'very short', 'short', 'tall']
    height_vars = [Int(f'height_{i}') for i in houses]
    for i in houses:
        solver.add(And(height_vars[i-1] >= 0, height_vars[i-1] < len(heights)))
    solver.add(Distinct(height_vars))
    
    cigars = ['prince', 'dunhill', 'blends', 'pall mall', 'blue master']
    cigar_vars = [Int(f'cigar_{i}') for i in houses]
    for i in houses:
        solver.add(And(cigar_vars[i-1] >= 0, cigar_vars[i-1] < len(cigars)))
    solver.add(Distinct(cigar_vars))
    
    smoothies = ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert']
    smoothie_vars = [Int(f'smoothie_{i}') for i in houses]
    for i in houses:
        solver.add(And(smoothie_vars[i-1] >= 0, smoothie_vars[i-1] < len(smoothies)))
    solver.add(Distinct(smoothie_vars))
    
    phones = ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6']
    phone_vars = [Int(f'phone_{i}') for i in houses]
    for i in houses:
        solver.add(And(phone_vars[i-1] >= 0, phone_vars[i-1] < len(phones)))
    solver.add(Distinct(phone_vars))
    
    # Helper functions
    def left_of(a, b):
        return Or([And(a == i, b == i+1) for i in range(1, n)])
    
    def right_of(a, b):
        return left_of(b, a)
    
    def next_to(a, b):
        return Or(left_of(a, b), right_of(a, b))
    
    # Get index values
    eric_idx = names.index('Eric')
    alice_idx = names.index('Alice')
    arnold_idx = names.index('Arnold')
    bob_idx = names.index('Bob')
    
    average_idx = heights.index('average')
    very_tall_idx = heights.index('very tall')
    very_short_idx = heights.index('very short')
    short_idx = heights.index('short')
    
    prince_idx = cigars.index('prince')
    dunhill_idx = cigars.index('dunhill')
    blends_idx = cigars.index('blends')
    blue_master_idx = cigars.index('blue master')
    
    desert_idx = smoothies.index('desert')
    cherry_idx = smoothies.index('cherry')
    dragonfruit_idx = smoothies.index('dragonfruit')
    lime_idx = smoothies.index('lime')
    
    iphone_idx = phones.index('iphone 13')
    huawei_idx = phones.index('huawei p50')
    oneplus_idx = phones.index('oneplus 9')
    samsung_idx = phones.index('samsung galaxy s21')
    
    # Clue 1: The Prince smoker is the Desert smoothie lover.
    for i in range(n):
        solver.add(Implies(cigar_vars[i] == prince_idx, smoothie_vars[i] == desert_idx))
    
    # Clue 2: There is one house between Eric and Alice.
    eric_pos = Int('eric_pos')
    alice_pos = Int('alice_pos')
    solver.add(eric_pos == Sum([If(name_vars[i] == eric_idx, i+1, 0) for i in range(n)]))
    solver.add(alice_pos == Sum([If(name_vars[i] == alice_idx, i+1, 0) for i in range(n)]))
    solver.add(Or(eric_pos + 2 == alice_pos, eric_pos - 2 == alice_pos))
    
    # Clue 3: The person who is short is the person who smokes many unique blends.
    for i in range(n):
        solver.add(Implies(height_vars[i] == short_idx, cigar_vars[i] == blends_idx))
    
    # Clue 4: The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
    for i in range(n-1):
        solver.add(Implies(phone_vars[i] == iphone_idx, cigar_vars[i+1] == blue_master_idx))
    
    # Clue 5: The person who has an average height is the Dunhill smoker.
    for i in range(n):
        solver.add(Implies(height_vars[i] == average_idx, cigar_vars[i] == dunhill_idx))
    
    # Clue 6: Eric is the person who is very tall.
    for i in range(n):
        solver.add(Implies(name_vars[i] == eric_idx, height_vars[i] == very_tall_idx))
    
    # Clue 7: Arnold is directly left of the person who uses a Huawei P50.
    for i in range(n-1):
        solver.add(Implies(name_vars[i] == arnold_idx, phone_vars[i+1] == huawei_idx))
    
    # Clue 8: Bob is not in the fourth house.
    solver.add(name_vars[3] != bob_idx)
    
    # Clue 9: Eric is directly left of the person who likes Cherry smoothies.
    for i in range(n-1):
        solver.add(Implies(name_vars[i] == eric_idx, smoothie_vars[i+1] == cherry_idx))
    
    # Clue 10: Bob is the Dunhill smoker.
    for i in range(n):
        solver.add(Implies(name_vars[i] == bob_idx, cigar_vars[i] == dunhill_idx))
    
    # Clue 11: The Dragonfruit smoothie lover is Bob.
    for i in range(n):
        solver.add(Implies(name_vars[i] == bob_idx, smoothie_vars[i] == dragonfruit_idx))
    
    # Clue 12: The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
    for i in range(n):
        if i == 0:  # First house
            solver.add(Implies(phone_vars[i] == iphone_idx, phone_vars[i+1] == oneplus_idx))
        elif i == n-1:  # Last house
            solver.add(Implies(phone_vars[i] == iphone_idx, phone_vars[i-1] == oneplus_idx))
        else:  # Middle houses
            solver.add(Implies(phone_vars[i] == iphone_idx, 
                              Or(phone_vars[i-1] == oneplus_idx, phone_vars[i+1] == oneplus_idx)))
    
    # Clue 13: The person who uses a Samsung Galaxy S21 is the person who is short.
    for i in range(n):
        solver.add(Implies(phone_vars[i] == samsung_idx, height_vars[i] == short_idx))
    
    # Clue 14: There are two houses between the person who is very tall and the Dragonfruit smoothie lover.
    very_tall_pos = Int('very_tall_pos')
    dragonfruit_pos = Int('dragonfruit_pos')
    solver.add(very_tall_pos == Sum([If(height_vars[i] == very_tall_idx, i+1, 0) for i in range(n)]))
    solver.add(dragonfruit_pos == Sum([If(smoothie_vars[i] == dragonfruit_idx, i+1, 0) for i in range(n)]))
    solver.add(Or(very_tall_pos + 3 == dragonfruit_pos, very_tall_pos - 3 == dragonfruit_pos))
    
    # Clue 15: The person who uses an iPhone 13 is Eric.
    for i in range(n):
        solver.add(Implies(phone_vars[i] == iphone_idx, name_vars[i] == eric_idx))
    
    # Clue 16: The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
    desert_pos = Int('desert_pos')
    lime_pos = Int('lime_pos')
    solver.add(desert_pos == Sum([If(smoothie_vars[i] == desert_idx, i+1, 0) for i in range(n)]))
    solver.add(lime_pos == Sum([If(smoothie_vars[i] == lime_idx, i+1, 0) for i in range(n)]))
    solver.add(desert_pos < lime_pos)
    
    # Clue 17: Arnold and the person who is very short are next to each other.
    arnold_pos = Int('arnold_pos')
    very_short_pos = Int('very_short_pos')
    solver.add(arnold_pos == Sum([If(name_vars[i] == arnold_idx, i+1, 0) for i in range(n)]))
    solver.add(very_short_pos == Sum([If(height_vars[i] == very_short_idx, i+1, 0) for i in range(n)]))
    solver.add(Or(arnold_pos + 1 == very_short_pos, arnold_pos - 1 == very_short_pos))
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        
        # Extract the solution
        solution = []
        for i in range(n):
            house_data = [str(i+1)]
            
            # Get name
            name_val = model.evaluate(name_vars[i]).as_long()
            house_data.append(names[name_val])
            
            # Get height
            height_val = model.evaluate(height_vars[i]).as_long()
            house_data.append(heights[height_val])
            
            # Get cigar
            cigar_val = model.evaluate(cigar_vars[i]).as_long()
            house_data.append(cigars[cigar_val])
            
            # Get smoothie
            smoothie_val = model.evaluate(smoothie_vars[i]).as_long()
            house_data.append(smoothies[smoothie_val])
            
            # Get phone
            phone_val = model.evaluate(phone_vars[i]).as_long()
            house_data.append(phones[phone_val])
            
            solution.append(house_data)
        
        # Format as JSON
        result = {
            "solution": {
                "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
                "rows": solution
            }
        }
        
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()