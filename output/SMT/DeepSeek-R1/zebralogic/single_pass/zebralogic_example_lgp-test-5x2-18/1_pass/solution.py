from z3 import *
import json

def main():
    s = Solver()
    
    # Define house variables for names
    Eric_h = Int('Eric_h')
    Alice_h = Int('Alice_h')
    Peter_h = Int('Peter_h')
    Bob_h = Int('Bob_h')
    Arnold_h = Int('Arnold_h')
    
    # Define house variables for children
    Timothy_h = Int('Timothy_h')
    Meredith_h = Int('Meredith_h')
    Samantha_h = Int('Samantha_h')
    Fred_h = Int('Fred_h')
    Bella_h = Int('Bella_h')
    
    # All name houses are between 1 and 5 and distinct
    name_houses = [Eric_h, Alice_h, Peter_h, Bob_h, Arnold_h]
    for h in name_houses:
        s.add(h >= 1, h <= 5)
    s.add(Distinct(name_houses))
    
    # All child houses are between 1 and 5 and distinct
    child_houses = [Timothy_h, Meredith_h, Samantha_h, Fred_h, Bella_h]
    for h in child_houses:
        s.add(h >= 1, h <= 5)
    s.add(Distinct(child_houses))
    
    # Clue 1: Bob is left of the person with child Samantha
    s.add(Bob_h < Samantha_h)
    
    # Clue 2: The mother of Timothy is left of the person with child Samantha
    s.add(Timothy_h < Samantha_h)
    
    # Clue 3: The person with child Fred is in house 2
    s.add(Fred_h == 2)
    
    # Clue 4: One house between Alice and the person with child Samantha
    s.add(Or(Alice_h == Samantha_h - 2, Alice_h == Samantha_h + 2))
    
    # Clue 5: Eric is not in the third house
    s.add(Eric_h != 3)
    
    # Clue 6: Bob is not in the third house
    s.add(Bob_h != 3)
    
    # Clue 7: Fred is directly left of Bella
    s.add(Fred_h == Bella_h - 1)
    
    # Clue 8: Samantha is left of Peter
    s.add(Samantha_h < Peter_h)
    
    if s.check() == sat:
        m = s.model()
        house_to_name = {}
        name_vars = [
            ('Eric', Eric_h),
            ('Alice', Alice_h),
            ('Peter', Peter_h),
            ('Bob', Bob_h),
            ('Arnold', Arnold_h)
        ]
        for name, var in name_vars:
            house = m[var].as_long()
            house_to_name[house] = name
        
        house_to_child = {}
        child_vars = [
            ('Timothy', Timothy_h),
            ('Meredith', Meredith_h),
            ('Samantha', Samantha_h),
            ('Fred', Fred_h),
            ('Bella', Bella_h)
        ]
        for child, var in child_vars:
            house = m[var].as_long()
            house_to_child[house] = child
        
        rows = []
        for house_num in range(1, 6):
            name = house_to_name.get(house_num)
            child = house_to_child.get(house_num)
            rows.append([str(house_num), name, child])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Children"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()