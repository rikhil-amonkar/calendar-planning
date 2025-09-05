from z3 import *
import json

def main():
    # Define the house indices (1 to 6)
    houses = [1, 2, 3, 4, 5, 6]
    n = len(houses)
    
    # Define enums for attributes
    Name, (Alice, Eric, Bob, Peter, Arnold, Carol) = EnumSort('Name', ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold', 'Carol'])
    Height, (very_tall, tall, super_tall, average, very_short, short) = EnumSort('Height', ['very_tall', 'tall', 'super_tall', 'average', 'very_short', 'short'])
    PhoneModel, (oneplus9, google_pixel6, samsung_galaxy_s21, iphone13, huawei_p50, xiaomi_mi11) = EnumSort('PhoneModel', ['oneplus9', 'google_pixel6', 'samsung_galaxy_s21', 'iphone13', 'huawei_p50', 'xiaomi_mi11'])
    
    # Create arrays for attributes per house
    name_vars = [Const(f'name_{i}', Name) for i in houses]
    height_vars = [Const(f'height_{i}', Height) for i in houses]
    phone_vars = [Const(f'phone_{i}', PhoneModel) for i in houses]
    
    s = Solver()
    
    # All attributes are distinct
    s.add(Distinct(name_vars))
    s.add(Distinct(height_vars))
    s.add(Distinct(phone_vars))
    
    # Clue 1: Bob is directly left of the person who is tall.
    for i in range(n-1):
        s.add(Implies(name_vars[i] == Bob, height_vars[i+1] == tall))
    
    # Clue 2: Peter is left of iPhone 13 user
    s.add(Or([And(name_vars[i] == Peter, phone_vars[j] == iphone13, i < j) for i in range(n) for j in range(n)]))
    
    # Clue 3: Very short is right of Google Pixel 6 user
    s.add(Or([And(phone_vars[i] == google_pixel6, height_vars[j] == very_short, i < j) for i in range(n) for j in range(n)]))
    
    # Clue 4: Carol is very tall
    for i in range(n):
        s.add(Implies(name_vars[i] == Carol, height_vars[i] == very_tall))
    
    # Clue 5: One house between Google Pixel 6 and short
    for i in range(n):
        for j in range(n):
            s.add(Implies(And(phone_vars[i] == google_pixel6, height_vars[j] == short), Abs(i - j) == 2))
    
    # Clue 6: Samsung Galaxy S21 not in first house
    s.add(phone_vars[0] != samsung_galaxy_s21)
    
    # Clue 7: OnePlus 9 directly left of short
    for i in range(n-1):
        s.add(Implies(phone_vars[i] == oneplus9, height_vars[i+1] == short))
    
    # Clue 8: Tall person is Arnold
    for i in range(n):
        s.add(Implies(height_vars[i] == tall, name_vars[i] == Arnold))
    
    # Clue 9: Super tall in first house
    s.add(height_vars[0] == super_tall)
    
    # Clue 10: Xiaomi Mi 11 user is Carol
    for i in range(n):
        s.add(Implies(phone_vars[i] == xiaomi_mi11, name_vars[i] == Carol))
    
    # Clue 11: Google Pixel 6 right of Eric
    s.add(Or([And(name_vars[i] == Eric, phone_vars[j] == google_pixel6, i < j) for i in range(n) for j in range(n)]))
    
    # Clue 12: Short in sixth house
    s.add(height_vars[5] == short)
    
    # Check satisfiability
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(n):
            name_val = m.eval(name_vars[i])
            height_val = m.eval(height_vars[i])
            phone_val = m.eval(phone_vars[i])
            
            # Convert to string representations
            if name_val.eq(Alice): name_str = "Alice"
            elif name_val.eq(Eric): name_str = "Eric"
            elif name_val.eq(Bob): name_str = "Bob"
            elif name_val.eq(Peter): name_str = "Peter"
            elif name_val.eq(Arnold): name_str = "Arnold"
            elif name_val.eq(Carol): name_str = "Carol"
            else: name_str = "Unknown"
            
            if height_val.eq(very_tall): height_str = "very tall"
            elif height_val.eq(tall): height_str = "tall"
            elif height_val.eq(super_tall): height_str = "super tall"
            elif height_val.eq(average): height_str = "average"
            elif height_val.eq(very_short): height_str = "very short"
            elif height_val.eq(short): height_str = "short"
            else: height_str = "Unknown"
            
            if phone_val.eq(oneplus9): phone_str = "oneplus 9"
            elif phone_val.eq(google_pixel6): phone_str = "google pixel 6"
            elif phone_val.eq(samsung_galaxy_s21): phone_str = "samsung galaxy s21"
            elif phone_val.eq(iphone13): phone_str = "iphone 13"
            elif phone_val.eq(huawei_p50): phone_str = "huawei p50"
            elif phone_val.eq(xiaomi_mi11): phone_str = "xiaomi mi 11"
            else: phone_str = "Unknown"
            
            rows.append([str(i+1), name_str, height_str, phone_str])
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Height", "PhoneModel"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()