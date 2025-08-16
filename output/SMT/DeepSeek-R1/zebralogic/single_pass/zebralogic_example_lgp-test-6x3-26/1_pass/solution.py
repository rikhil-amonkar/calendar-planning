from z3 import *
import json

def main():
    # Define the enums for attributes
    Name = Enum('Name', ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold', 'Carol'])
    Height = Enum('Height', ['very_tall', 'tall', 'super_tall', 'average', 'very_short', 'short'])
    PhoneModel = Enum('PhoneModel', ['oneplus_9', 'google_pixel_6', 'samsung_galaxy_s21', 'iphone_13', 'huawei_p50', 'xiaomi_mi_11'])
    
    houses = [0, 1, 2, 3, 4, 5]  # indices for houses 1 to 6

    # Create variables for each house
    names = [Const('name_%d' % i, Name) for i in houses]
    heights = [Const('height_%d' % i, Height) for i in houses]
    phones = [Const('phone_%d' % i, PhoneModel) for i in houses]
    
    s = Solver()
    
    # Distinct constraints
    s.add(Distinct(names))
    s.add(Distinct(heights))
    s.add(Distinct(phones))
    
    # Fixed constraints from clues and deductions
    s.add(heights[0] == Height.super_tall)   # house1: super tall (clue9)
    s.add(heights[5] == Height.short)         # house6: short (clue12)
    s.add(phones[3] == PhoneModel.google_pixel_6)  # house4: Google Pixel 6 (deduced from clues 5,7,12)
    s.add(phones[4] == PhoneModel.oneplus_9)       # house5: OnePlus 9 (deduced from clues 5,7,12)
    s.add(heights[4] == Height.very_short)         # house5: very short (deduced from clues 3,12)
    
    # Clue1: Bob is directly left of the person who is tall (and tall is Arnold by clue8)
    s.add(Or([And(names[i] == Name.Bob, names[i+1] == Name.Arnold, heights[i+1] == Height.tall) for i in range(0,5)]))
    
    # Clue2: Peter is left of the iPhone 13 user
    s.add(Or([And(names[i] == Name.Peter, phones[j] == PhoneModel.iphone_13, i < j) for i in range(6) for j in range(6)]))
    
    # Clue3: very_short is right of Google Pixel 6
    s.add(Or([And(phones[i] == PhoneModel.google_pixel_6, heights[j] == Height.very_short, i < j) for i in range(6) for j in range(6)]))
    
    # Clue4: Carol is very_tall
    s.add(Or([And(names[i] == Name.Carol, heights[i] == Height.very_tall) for i in range(6)]))
    
    # Clue5: One house between Google Pixel 6 and short
    s.add(Or(
        [And(phones[i] == PhoneModel.google_pixel_6, heights[j] == Height.short, j == i+2) for i in range(4)],
        [And(phones[i] == PhoneModel.google_pixel_6, heights[j] == Height.short, i == j+2) for j in range(4)]
    ))
    
    # Clue6: Samsung Galaxy S21 not in house1
    s.add(phones[0] != PhoneModel.samsung_galaxy_s21)
    
    # Clue7: OnePlus 9 directly left of short
    s.add(Or([And(phones[i] == PhoneModel.oneplus_9, heights[i+1] == Height.short) for i in range(5)]))
    
    # Clue8: Tall is Arnold
    s.add(Or([And(heights[i] == Height.tall, names[i] == Name.Arnold) for i in range(6)]))
    
    # Clue10: Carol uses Xiaomi Mi 11
    s.add(Or([And(names[i] == Name.Carol, phones[i] == PhoneModel.xiaomi_mi_11) for i in range(6)]))
    
    # Clue11: Google Pixel 6 is right of Eric
    s.add(Or([And(names[i] == Name.Eric, phones[j] == PhoneModel.google_pixel_6, i < j) for i in range(6) for j in range(6)]))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        
        # Mapping from enum strings to original problem strings
        height_map = {
            'very_tall': 'very tall',
            'tall': 'tall',
            'super_tall': 'super tall',
            'average': 'average',
            'very_short': 'very short',
            'short': 'short'
        }
        phone_map = {
            'oneplus_9': 'oneplus 9',
            'google_pixel_6': 'google pixel 6',
            'samsung_galaxy_s21': 'samsung galaxy s21',
            'iphone_13': 'iphone 13',
            'huawei_p50': 'huawei p50',
            'xiaomi_mi_11': 'xiaomi mi 11'
        }
        
        # Build the result dictionary
        result = {
            "solution": {
                "header": ["House", "Name", "Height", "PhoneModel"],
                "rows": []
            }
        }
        
        for i in range(6):
            house_num = str(i+1)
            n_val = m.eval(names[i])
            h_val = m.eval(heights[i])
            p_val = m.eval(phones[i])
            
            n_str = str(n_val)
            h_str = height_map[str(h_val)]
            p_str = phone_map[str(p_val)]
            
            result["solution"]["rows"].append([house_num, n_str, h_str, p_str])
        
        # Output as JSON
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()