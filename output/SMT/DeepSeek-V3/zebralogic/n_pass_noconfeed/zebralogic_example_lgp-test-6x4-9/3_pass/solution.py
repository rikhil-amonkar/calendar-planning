from z3 import *
import json

def main():
    # Create solver
    s = Solver()
    
    # Define the number of houses
    n = 6
    houses = list(range(n))  # Use 0-indexed for easier array access
    
    # Define attributes
    names = ['Carol', 'Bob', 'Alice', 'Arnold', 'Eric', 'Peter']
    phones = ['samsung galaxy s21', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9', 'xiaomi mi 11']
    nationalities = ['swede', 'chinese', 'norwegian', 'dane', 'german', 'brit']
    colors = ['blue', 'red', 'yellow', 'green', 'white', 'purple']
    
    # Create variables for each attribute per house
    name_vars = [Int(f"name_{i}") for i in range(n)]
    phone_vars = [Int(f"phone_{i}") for i in range(n)]
    nationality_vars = [Int(f"nationality_{i}") for i in range(n)]
    color_vars = [Int(f"color_{i}") for i in range(n)]
    
    # Constrain each variable to be within the index range of its attribute list
    for i in range(n):
        s.add(And(name_vars[i] >= 0, name_vars[i] < len(names)))
        s.add(And(phone_vars[i] >= 0, phone_vars[i] < len(phones)))
        s.add(And(nationality_vars[i] >= 0, nationality_vars[i] < len(nationalities)))
        s.add(And(color_vars[i] >= 0, color_vars[i] < len(colors)))
    
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
    dane_brit_constraint = Or(
        And(nationality_vars[0] == idx(nationalities, 'dane'), nationality_vars[2] == idx(nationalities, 'brit')),
        And(nationality_vars[0] == idx(nationalities, 'brit'), nationality_vars[2] == idx(nationalities, 'dane')),
        And(nationality_vars[1] == idx(nationalities, 'dane'), nationality_vars[3] == idx(nationalities, 'brit')),
        And(nationality_vars[1] == idx(nationalities, 'brit'), nationality_vars[3] == idx(nationalities, 'dane')),
        And(nationality_vars[2] == idx(nationalities, 'dane'), nationality_vars[4] == idx(nationalities, 'brit')),
        And(nationality_vars[2] == idx(nationalities, 'brit'), nationality_vars[4] == idx(nationalities, 'dane')),
        And(nationality_vars[3] == idx(nationalities, 'dane'), nationality_vars[5] == idx(nationalities, 'brit')),
        And(nationality_vars[3] == idx(nationalities, 'brit'), nationality_vars[5] == idx(nationalities, 'dane'))
    )
    s.add(dane_brit_constraint)
    
    # Clue 3: Carol is the person whose favorite color is green.
    for i in range(n):
        s.add(Implies(name_vars[i] == idx(names, 'Carol'), color_vars[i] == idx(colors, 'green')))
    
    # Clue 4: Arnold is directly left of Alice.
    arnold_alice_constraint = Or()
    for i in range(n-1):
        arnold_alice_constraint = Or(arnold_alice_constraint, 
                                   And(name_vars[i] == idx(names, 'Arnold'), name_vars[i+1] == idx(names, 'Alice')))
    s.add(arnold_alice_constraint)
    
    # Clue 5: Alice is the German.
    for i in range(n):
        s.add(Implies(name_vars[i] == idx(names, 'Alice'), nationality_vars[i] == idx(nationalities, 'german')))
    
    # Clue 6: The person who uses a OnePlus 9 is the person who loves purple.
    for i in range(n):
        s.add(Implies(phone_vars[i] == idx(phones, 'oneplus 9'), color_vars[i] == idx(colors, 'purple')))
    
    # Clue 7: The person who uses a Huawei P50 is not in the third house.
    s.add(phone_vars[2] != idx(phones, 'huawei p50'))
    
    # Clue 8: The person who uses a Samsung Galaxy S21 is in the fifth house.
    s.add(phone_vars[4] == idx(phones, 'samsung galaxy s21'))
    
    # Clue 9: The person who loves white is somewhere to the right of the person whose favorite color is red.
    white_right_of_red = Or()
    for i in range(n):
        for j in range(i+1, n):
            white_right_of_red = Or(white_right_of_red, 
                                  And(color_vars[i] == idx(colors, 'red'), color_vars[j] == idx(colors, 'white')))
    s.add(white_right_of_red)
    
    # Clue 10: The person who uses a Samsung Galaxy S21 is Bob.
    for i in range(n):
        s.add(Implies(phone_vars[i] == idx(phones, 'samsung galaxy s21'), name_vars[i] == idx(names, 'Bob')))
    
    # Clue 11: The Dane is the person who loves yellow.
    for i in range(n):
        s.add(Implies(nationality_vars[i] == idx(nationalities, 'dane'), color_vars[i] == idx(colors, 'yellow')))
    
    # Clue 12: The person who uses a Samsung Galaxy S21 is somewhere to the left of Peter.
    samsung_left_of_peter = Or()
    for i in range(n):
        for j in range(i+1, n):
            samsung_left_of_peter = Or(samsung_left_of_peter, 
                                     And(phone_vars[i] == idx(phones, 'samsung galaxy s21'), name_vars[j] == idx(names, 'Peter')))
    s.add(samsung_left_of_peter)
    
    # Clue 13: The person who loves blue is Peter.
    for i in range(n):
        s.add(Implies(color_vars[i] == idx(colors, 'blue'), name_vars[i] == idx(names, 'Peter')))
    
    # Clue 14: Peter is the British person.
    for i in range(n):
        s.add(Implies(name_vars[i] == idx(names, 'Peter'), nationality_vars[i] == idx(nationalities, 'brit')))
    
    # Clue 15: The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    # Since Samsung is in house 5 (0-indexed 4), iPhone must be in house 6 (0-indexed 5)
    s.add(phone_vars[5] == idx(phones, 'iphone 13'))
    
    # Clue 16: The Norwegian is the person who loves purple.
    for i in range(n):
        s.add(Implies(nationality_vars[i] == idx(nationalities, 'norwegian'), color_vars[i] == idx(colors, 'purple')))
    
    # Clue 17: The person who uses a Xiaomi Mi 11 is the Chinese.
    for i in range(n):
        s.add(Implies(phone_vars[i] == idx(phones, 'xiaomi mi 11'), nationality_vars[i] == idx(nationalities, 'chinese')))
    
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
        for i in range(n):
            name_idx = m.evaluate(name_vars[i]).as_long()
            phone_idx = m.evaluate(phone_vars[i]).as_long()
            nationality_idx = m.evaluate(nationality_vars[i]).as_long()
            color_idx = m.evaluate(color_vars[i]).as_long()
            
            row = [
                str(i+1),  # House numbers start from 1
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