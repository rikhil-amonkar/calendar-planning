from z3 import *
import json

def main():
    # Define the mappings for each attribute
    names = ['Carol', 'Bob', 'Alice', 'Arnold', 'Eric', 'Peter']
    name_map = {name: idx for idx, name in enumerate(names)}
    name_rev = {idx: name for idx, name in enumerate(names)}
    
    phones = ['samsung galaxy s21', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9', 'xiaomi mi 11']
    phone_map = {phone: idx for idx, phone in enumerate(phones)}
    phone_rev = {idx: phone for idx, phone in enumerate(phones)}
    
    nations = ['swede', 'chinese', 'norwegian', 'dane', 'german', 'brit']
    nation_map = {nation: idx for idx, nation in enumerate(nations)}
    nation_rev = {idx: nation for idx, nation in enumerate(nations)}
    
    colors = ['blue', 'red', 'yellow', 'green', 'white', 'purple']
    color_map = {color: idx for idx, color in enumerate(colors)}
    color_rev = {idx: color for idx, color in enumerate(colors)}
    
    # Create arrays for attributes of each house (0 to 5 for houses 1 to 6)
    name = [Int(f'name_{i}') for i in range(6)]
    phone = [Int(f'phone_{i}') for i in range(6)]
    nation = [Int(f'nation_{i}') for i in range(6)]
    color = [Int(f'color_{i}') for i in range(6)]
    
    s = Solver()
    
    # Fixed values from clues
    s.add(nation[3] == nation_map['dane'])
    s.add(color[3] == color_map['yellow'])
    s.add(name[4] == name_map['Bob'])
    s.add(phone[4] == phone_map['samsung galaxy s21'])
    s.add(name[5] == name_map['Peter'])
    s.add(color[5] == color_map['blue'])
    s.add(nation[5] == nation_map['brit'])
    s.add(phone[5] == phone_map['iphone 13'])
    
    # Distinct constraints for each attribute
    s.add(Distinct(name))
    s.add(Distinct(phone))
    s.add(Distinct(nation))
    s.add(Distinct(color))
    
    # Each attribute value is between 0 and 5
    for i in range(6):
        s.add(name[i] >= 0, name[i] < 6)
        s.add(phone[i] >= 0, phone[i] < 6)
        s.add(nation[i] >= 0, nation[i] < 6)
        s.add(color[i] >= 0, color[i] < 6)
    
    # Clue 1: Carol is not in the third house (index2)
    s.add(name[2] != name_map['Carol'])
    
    # Clue 3: Carol's favorite color is green
    for i in range(6):
        s.add((name[i] == name_map['Carol']) == (color[i] == color_map['green']))
    
    # Clue 4: Arnold is directly left of Alice
    s.add(Or([And(name[i] == name_map['Arnold'], name[i+1] == name_map['Alice']) for i in range(5)]))
    
    # Clue 5: Alice is the German
    for i in range(6):
        s.add((name[i] == name_map['Alice']) == (nation[i] == nation_map['german']))
    
    # Clue 6: OnePlus 9 user loves purple
    for i in range(6):
        s.add((phone[i] == phone_map['oneplus 9']) == (color[i] == color_map['purple']))
    
    # Clue 7: Huawei P50 not in third house
    s.add(phone[2] != phone_map['huawei p50'])
    
    # Clue 9: White is right of red
    for i in range(5):
        s.add(Implies(color[i] == color_map['red'], 
                      Or([color[j] == color_map['white'] for j in range(i+1, 6)])))
    
    # Clue 11: Dane loves yellow
    for i in range(6):
        s.add((nation[i] == nation_map['dane']) == (color[i] == color_map['yellow']))
    
    # Clue 16: Norwegian loves purple
    for i in range(6):
        s.add((nation[i] == nation_map['norwegian']) == (color[i] == color_map['purple']))
    
    # Clue 17: Xiaomi Mi 11 user is Chinese
    for i in range(6):
        s.add((phone[i] == phone_map['xiaomi mi 11']) == (nation[i] == nation_map['chinese']))
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(6):
            n_val = m[name[i]].as_long()
            p_val = m[phone[i]].as_long()
            na_val = m[nation[i]].as_long()
            c_val = m[color[i]].as_long()
            row = [str(i+1), name_rev[n_val], phone_rev[p_val], nation_rev[na_val], color_rev[c_val]]
            rows.append(row)
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()