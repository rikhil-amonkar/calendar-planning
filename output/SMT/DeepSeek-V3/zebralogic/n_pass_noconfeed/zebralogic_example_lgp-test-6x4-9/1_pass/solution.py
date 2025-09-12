from z3 import *
import json

def main():
    # Create solver
    s = Solver()
    
    # Define the number of houses
    n = 6
    houses = [1, 2, 3, 4, 5, 6]
    
    # Define attributes
    names = ['Carol', 'Bob', 'Alice', 'Arnold', 'Eric', 'Peter']
    phones = ['samsung galaxy s21', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9', 'xiaomi mi 11']
    nationalities = ['swede', 'chinese', 'norwegian', 'dane', 'german', 'brit']
    colors = ['blue', 'red', 'yellow', 'green', 'white', 'purple']
    
    # Create variables for each attribute per house
    name_vars = [Int(f"name_{i}") for i in houses]
    phone_vars = [Int(f"phone_{i}") for i in houses]
    nationality_vars = [Int(f"nationality_{i}") for i in houses]
    color_vars = [Int(f"color_{i}") for i in houses]
    
    # Constrain each variable to be within the index range of its attribute list
    for i in houses:
        s.add(And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        s.add(And(phone_vars[i-1] >= 0, phone_vars[i-1] < len(phones)))
        s.add(And(nationality_vars[i-1] >= 0, nationality_vars[i-1] < len(nationalities)))
        s.add(And(color_vars[i-1] >= 0, color_vars[i-1] < len(colors)))
    
    # All attributes are distinct per house
    s.add(Distinct(name_vars))
    s.add(Distinct(phone_vars))
    s.add(Distinct(nationality_vars))
    s.add(Distinct(color_vars))
    
    # Helper function to get index of a value in a list
    def idx(lst, val):
        return lst.index(val)
    
    # Clue 1: Carol is not in the third house.
    s.add(name_vars[2] != idx(names, 'Carol'))
    
    # Clue 2: There is one house between the Dane and the British person.
    for i in range(1, n-1):
        s.add(Implies(nationality_vars[i-1] == idx(nationalities, 'dane'), nationality_vars[i+1] == idx(nationalities, 'brit')))
        s.add(Implies(nationality_vars[i+1] == idx(nationalities, 'dane'), nationality_vars[i-1] == idx(nationalities, 'brit')))
    
    # Clue 3: Carol is the person whose favorite color is green.
    for i in houses:
        s.add(Implies(name_vars[i-1] == idx(names, 'Carol'), color_vars[i-1] == idx(colors, 'green')))
    
    # Clue 4: Arnold is directly left of Alice.
    for i in range(1, n):
        s.add(Implies(name_vars[i-1] == idx(names, 'Arnold'), name_vars[i] == idx(names, 'Alice')))
    
    # Clue 5: Alice is the German.
    for i in houses:
        s.add(Implies(name_vars[i-1] == idx(names, 'Alice'), nationality_vars[i-1] == idx(nationalities, 'german')))
    
    # Clue 6: The person who uses a OnePlus 9 is the person who loves purple.
    for i in houses:
        s.add(Implies(phone_vars[i-1] == idx(phones, 'oneplus 9'), color_vars[i-1] == idx(colors, 'purple')))
    
    # Clue 7: The person who uses a Huawei P50 is not in the third house.
    s.add(phone_vars[2] != idx(phones, 'huawei p50'))
    
    # Clue 8: The person who uses a Samsung Galaxy S21 is in the fifth house.
    s.add(phone_vars[4] == idx(phones, 'samsung galaxy s21'))
    
    # Clue 9: The person who loves white is somewhere to the right of the person whose favorite color is red.
    for i in houses:
        for j in range(i, n):
            s.add(Implies(color_vars[i-1] == idx(colors, 'red'), color_vars[j] == idx(colors, 'white')))
    
    # Clue 10: The person who uses a Samsung Galaxy S21 is Bob.
    for i in houses:
        s.add(Implies(phone_vars[i-1] == idx(phones, 'samsung galaxy s21'), name_vars[i-1] == idx(names, 'Bob')))
    
    # Clue 11: The Dane is the person who loves yellow.
    for i in houses:
        s.add(Implies(nationality_vars[i-1] == idx(nationalities, 'dane'), color_vars[i-1] == idx(colors, 'yellow')))
    
    # Clue 12: The person who uses a Samsung Galaxy S21 is somewhere to the left of Peter.
    for i in houses:
        for j in range(i, n):
            s.add(Implies(phone_vars[i-1] == idx(phones, 'samsung galaxy s21'), name_vars[j] == idx(names, 'Peter')))
    
    # Clue 13: The person who loves blue is Peter.
    for i in houses:
        s.add(Implies(color_vars[i-1] == idx(colors, 'blue'), name_vars[i-1] == idx(names, 'Peter')))
    
    # Clue 14: Peter is the British person.
    for i in houses:
        s.add(Implies(name_vars[i-1] == idx(names, 'Peter'), nationality_vars[i-1] == idx(nationalities, 'brit')))
    
    # Clue 15: The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    s.add(phone_vars[5] == idx(phones, 'iphone 13'))  # Since Samsung is in house 5, iPhone must be in house 6
    
    # Clue 16: The Norwegian is the person who loves purple.
    for i in houses:
        s.add(Implies(nationality_vars[i-1] == idx(nationalities, 'norwegian'), color_vars[i-1] == idx(colors, 'purple')))
    
    # Clue 17: The person who uses a Xiaomi Mi 11 is the Chinese.
    for i in houses:
        s.add(Implies(phone_vars[i-1] == idx(phones, 'xiaomi mi 11'), nationality_vars[i-1] == idx(nationalities, 'chinese')))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        
        # Create result structure
        result = {
            "solution": {
                "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
                "rows": []
            }
        }
        
        # Collect values for each house
        for i in houses:
            name_idx = m.evaluate(name_vars[i-1]).as_long()
            phone_idx = m.evaluate(phone_vars[i-1]).as_long()
            nationality_idx = m.evaluate(nationality_vars[i-1]).as_long()
            color_idx = m.evaluate(color_vars[i-1]).as_long()
            
            row = [
                str(i),
                names[name_idx],
                phones[phone_idx],
                nationalities[nationality_idx],
                colors[color_idx]
            ]
            result["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()