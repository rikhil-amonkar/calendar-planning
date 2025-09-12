import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    n_houses = 6
    houses = list(range(1, n_houses+1))
    
    # Define attributes
    names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold', 'Carol']
    heights = ['very tall', 'tall', 'super tall', 'average', 'very short', 'short']
    phones = ['oneplus 9', 'google pixel 6', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'xiaomi mi 11']
    
    # Create variables for each attribute per house
    name_vars = [z3.Int(f'name_{i}') for i in houses]
    height_vars = [z3.Int(f'height_{i}') for i in houses]
    phone_vars = [z3.Int(f'phone_{i}') for i in houses]
    
    # Constraint: All attributes are within valid range (0-5)
    for i in houses:
        solver.add(z3.And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(z3.And(height_vars[i-1] >= 0, height_vars[i-1] < len(heights)))
        solver.add(z3.And(phone_vars[i-1] >= 0, phone_vars[i-1] < len(phones)))
    
    # Constraint: All attributes are distinct within their category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(height_vars))
    solver.add(z3.Distinct(phone_vars))
    
    # Helper function to get index of a value in a list
    def idx(lst, val):
        return lst.index(val)
    
    # Get indices for all values
    alice_idx = idx(names, 'Alice')
    eric_idx = idx(names, 'Eric')
    bob_idx = idx(names, 'Bob')
    peter_idx = idx(names, 'Peter')
    arnold_idx = idx(names, 'Arnold')
    carol_idx = idx(names, 'Carol')
    
    very_tall_idx = idx(heights, 'very tall')
    tall_idx = idx(heights, 'tall')
    super_tall_idx = idx(heights, 'super tall')
    average_idx = idx(heights, 'average')
    very_short_idx = idx(heights, 'very short')
    short_idx = idx(heights, 'short')
    
    oneplus_idx = idx(phones, 'oneplus 9')
    pixel_idx = idx(phones, 'google pixel 6')
    samsung_idx = idx(phones, 'samsung galaxy s21')
    iphone_idx = idx(phones, 'iphone 13')
    huawei_idx = idx(phones, 'huawei p50')
    xiaomi_idx = idx(phones, 'xiaomi mi 11')
    
    # Clue 1: Bob is directly left of the person who is tall.
    # This means Bob is immediately left of the tall person
    bob_left_of_tall = []
    for i in range(n_houses - 1):
        bob_left_of_tall.append(z3.And(name_vars[i] == bob_idx, height_vars[i+1] == tall_idx))
    solver.add(z3.Or(bob_left_of_tall))
    
    # Clue 2: Peter is somewhere to the left of the person who uses an iPhone 13.
    peter_left_of_iphone = []
    for i in range(n_houses):
        for j in range(i+1, n_houses):
            peter_left_of_iphone.append(z3.And(name_vars[i] == peter_idx, phone_vars[j] == iphone_idx))
    solver.add(z3.Or(peter_left_of_iphone))
    
    # Clue 3: The person who is very short is somewhere to the right of the person who uses a Google Pixel 6.
    very_short_right_of_pixel = []
    for i in range(n_houses):
        for j in range(i):
            very_short_right_of_pixel.append(z3.And(height_vars[i] == very_short_idx, phone_vars[j] == pixel_idx))
    solver.add(z3.Or(very_short_right_of_pixel))
    
    # Clue 4: Carol is the person who is very tall.
    for i in range(n_houses):
        solver.add(z3.Implies(name_vars[i] == carol_idx, height_vars[i] == very_tall_idx))
        solver.add(z3.Implies(height_vars[i] == very_tall_idx, name_vars[i] == carol_idx))
    
    # Clue 5: There is one house between the person who uses a Google Pixel 6 and the person who is short.
    pixel_short_distance = []
    for i in range(n_houses):
        for j in range(n_houses):
            if abs(i - j) == 2:  # One house between means distance of 2
                pixel_short_distance.append(z3.And(phone_vars[i] == pixel_idx, height_vars[j] == short_idx))
    solver.add(z3.Or(pixel_short_distance))
    
    # Clue 6: The person who uses a Samsung Galaxy S21 is not in the first house.
    solver.add(phone_vars[0] != samsung_idx)
    
    # Clue 7: The person who uses a OnePlus 9 is directly left of the person who is short.
    for i in range(n_houses-1):
        solver.add(z3.Implies(phone_vars[i] == oneplus_idx, height_vars[i+1] == short_idx))
    
    # Clue 8: The person who is tall is Arnold.
    for i in range(n_houses):
        solver.add(z3.Implies(height_vars[i] == tall_idx, name_vars[i] == arnold_idx))
        solver.add(z3.Implies(name_vars[i] == arnold_idx, height_vars[i] == tall_idx))
    
    # Clue 9: The person who is super tall is in the first house.
    solver.add(height_vars[0] == super_tall_idx)
    
    # Clue 10: The person who uses a Xiaomi Mi 11 is Carol.
    for i in range(n_houses):
        solver.add(z3.Implies(phone_vars[i] == xiaomi_idx, name_vars[i] == carol_idx))
        solver.add(z3.Implies(name_vars[i] == carol_idx, phone_vars[i] == xiaomi_idx))
    
    # Clue 11: The person who uses a Google Pixel 6 is somewhere to the right of Eric.
    pixel_right_of_eric = []
    for i in range(n_houses):
        for j in range(i):
            pixel_right_of_eric.append(z3.And(phone_vars[i] == pixel_idx, name_vars[j] == eric_idx))
    solver.add(z3.Or(pixel_right_of_eric))
    
    # Clue 12: The person who is short is in the sixth house.
    solver.add(height_vars[5] == short_idx)
    
    # Check satisfiability
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Create result structure
        result = {
            "solution": {
                "header": ["House", "Name", "Height", "PhoneModel"],
                "rows": []
            }
        }
        
        # Extract values from model
        for i in range(n_houses):
            name_val = model.eval(name_vars[i]).as_long()
            height_val = model.eval(height_vars[i]).as_long()
            phone_val = model.eval(phone_vars[i]).as_long()
            
            row = [
                str(i+1),
                names[name_val],
                heights[height_val],
                phones[phone_val]
            ]
            result["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()