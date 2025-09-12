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
    def get_house_index(var_array, value):
        return [If(var_array[i] == value, i+1, 0) for i in range(n)]
    
    def left_of(a, b):
        return Or([And(a == i, b == i+1) for i in range(1, n)])
    
    def right_of(a, b):
        return left_of(b, a)
    
    def next_to(a, b):
        return Or(left_of(a, b), right_of(a, b))
    
    def between(a, b, c):
        return Or(And(a < b, b < c), And(c < b, b < a))
    
    # Clue 1: The Prince smoker is the Desert smoothie lover.
    prince_idx = cigars.index('prince')
    desert_idx = smoothies.index('desert')
    for i in range(n):
        solver.add(Implies(cigar_vars[i] == prince_idx, smoothie_vars[i] == desert_idx))
    
    # Clue 2: There is one house between Eric and Alice.
    eric_idx = names.index('Eric')
    alice_idx = names.index('Alice')
    solver.add(Or(
        And([If(name_vars[i] == eric_idx, 1, 0) for i in range(n)] == [1,0,0,0,0],
            [If(name_vars[i] == alice_idx, 1, 0) for i in range(n)] == [0,0,1,0,0]),
        And([If(name_vars[i] == eric_idx, 1, 0) for i in range(n)] == [0,1,0,0,0],
            [If(name_vars[i] == alice_idx, 1, 0) for i in range(n)] == [0,0,0,1,0]),
        And([If(name_vars[i] == eric_idx, 1, 0) for i in range(n)] == [0,0,1,0,0],
            [If(name_vars[i] == alice_idx, 1, 0) for i in range(n)] == [1,0,0,0,0]),
        And([If(name_vars[i] == eric_idx, 1, 0) for i in range(n)] == [0,0,0,1,0],
            [If(name_vars[i] == alice_idx, 1, 0) for i in range(n)] == [0,1,0,0,0]),
        And([If(name_vars[i] == eric_idx, 1, 0) for i in range(n)] == [0,0,1,0,0],
            [If(name_vars[i] == alice_idx, 1, 0) for i in range(n)] == [0,0,0,0,1]),
        And([If(name_vars[i] == eric_idx, 1, 0) for i in range(n)] == [0,0,0,0,1],
            [If(name_vars[i] == alice_idx, 1, 0) for i in range(n)] == [0,0,1,0,0]),
        And([If(name_vars[i] == eric_idx, 1, 0) for i in range(n)] == [0,0,0,1,0],
            [If(name_vars[i] == alice_idx, 1, 0) for i in range(n)] == [0,0,0,0,1]),
        And([If(name_vars[i] == eric_idx, 1, 0) for i in range(n)] == [0,0,0,0,1],
            [If(name_vars[i] == alice_idx, 1, 0) for i in range(n)] == [0,0,0,1,0])
    ))
    
    # Clue 3: The person who is short is the person who smokes many unique blends.
    short_idx = heights.index('short')
    blends_idx = cigars.index('blends')
    for i in range(n):
        solver.add(Implies(height_vars[i] == short_idx, cigar_vars[i] == blends_idx))
    
    # Clue 4: The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
    iphone_idx = phones.index('iphone 13')
    blue_master_idx = cigars.index('blue master')
    for i in range(n-1):
        solver.add(Implies(phone_vars[i] == iphone_idx, cigar_vars[i+1] == blue_master_idx))
    
    # Clue 5: The person who has an average height is the Dunhill smoker.
    average_idx = heights.index('average')
    dunhill_idx = cigars.index('dunhill')
    for i in range(n):
        solver.add(Implies(height_vars[i] == average_idx, cigar_vars[i] == dunhill_idx))
    
    # Clue 6: Eric is the person who is very tall.
    very_tall_idx = heights.index('very tall')
    for i in range(n):
        solver.add(Implies(name_vars[i] == eric_idx, height_vars[i] == very_tall_idx))
    
    # Clue 7: Arnold is directly left of the person who uses a Huawei P50.
    arnold_idx = names.index('Arnold')
    huawei_idx = phones.index('huawei p50')
    for i in range(n-1):
        solver.add(Implies(name_vars[i] == arnold_idx, phone_vars[i+1] == huawei_idx))
    
    # Clue 8: Bob is not in the fourth house.
    bob_idx = names.index('Bob')
    solver.add(name_vars[3] != bob_idx)
    
    # Clue 9: Eric is directly left of the person who likes Cherry smoothies.
    cherry_idx = smoothies.index('cherry')
    for i in range(n-1):
        solver.add(Implies(name_vars[i] == eric_idx, smoothie_vars[i+1] == cherry_idx))
    
    # Clue 10: Bob is the Dunhill smoker.
    for i in range(n):
        solver.add(Implies(name_vars[i] == bob_idx, cigar_vars[i] == dunhill_idx))
    
    # Clue 11: The Dragonfruit smoothie lover is Bob.
    dragonfruit_idx = smoothies.index('dragonfruit')
    for i in range(n):
        solver.add(Implies(name_vars[i] == bob_idx, smoothie_vars[i] == dragonfruit_idx))
    
    # Clue 12: The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
    oneplus_idx = phones.index('oneplus 9')
    for i in range(n):
        if i > 0:
            solver.add(Implies(phone_vars[i] == iphone_idx, 
                              Or(phone_vars[i-1] == oneplus_idx, 
                                 If(i < n-1, phone_vars[i+1] == oneplus_idx, False))))
        if i < n-1:
            solver.add(Implies(phone_vars[i] == oneplus_idx, 
                              Or(phone_vars[i-1] == iphone_idx, 
                                 If(i < n-1, phone_vars[i+1] == iphone_idx, False))))
    
    # Clue 13: The person who uses a Samsung Galaxy S21 is the person who is short.
    samsung_idx = phones.index('samsung galaxy s21')
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
    lime_idx = smoothies.index('lime')
    desert_pos = Int('desert_pos')
    lime_pos = Int('lime_pos')
    solver.add(desert_pos == Sum([If(smoothie_vars[i] == desert_idx, i+1, 0) for i in range(n)]))
    solver.add(lime_pos == Sum([If(smoothie_vars[i] == lime_idx, i+1, 0) for i in range(n)]))
    solver.add(desert_pos < lime_pos)
    
    # Clue 17: Arnold and the person who is very short are next to each other.
    very_short_idx = heights.index('very short')
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