from z3 import *
import json

def main():
    # Define the variables for the house numbers of each name and child
    Eric_house = Int('Eric_house')
    Alice_house = Int('Alice_house')
    Peter_house = Int('Peter_house')
    Bob_house = Int('Bob_house')
    Arnold_house = Int('Arnold_house')
    
    Timothy_house = Int('Timothy_house')
    Meredith_house = Int('Meredith_house')
    Samantha_house = Int('Samantha_house')
    Fred_house = Int('Fred_house')
    Bella_house = Int('Bella_house')
    
    s = Solver()
    
    # All houses are between 1 and 5
    houses = [Eric_house, Alice_house, Peter_house, Bob_house, Arnold_house,
              Timothy_house, Meredith_house, Samantha_house, Fred_house, Bella_house]
    for h in houses:
        s.add(h >= 1, h <= 5)
    
    # Names are in distinct houses
    s.add(Distinct(Eric_house, Alice_house, Peter_house, Bob_house, Arnold_house))
    # Children are in distinct houses
    s.add(Distinct(Timothy_house, Meredith_house, Samantha_house, Fred_house, Bella_house))
    
    # Clue 1: Bob is left of the child Samantha
    s.add(Bob_house < Samantha_house)
    
    # Clue 2: Mother of Timothy is left of the child Samantha
    s.add(Timothy_house < Samantha_house)
    
    # Clue 3: Child Fred is in second house
    s.add(Fred_house == 2)
    
    # Clue 4: One house between Alice and child Samantha
    s.add(Or(Alice_house == Samantha_house - 2, Alice_house == Samantha_house + 2))
    
    # Clue 5: Eric not in third house
    s.add(Eric_house != 3)
    
    # Clue 6: Bob not in third house
    s.add(Bob_house != 3)
    
    # Clue 7: Child Fred directly left of child Bella
    s.add(Fred_house == Bella_house - 1)
    
    # Clue 8: Child Samantha left of Peter
    s.add(Samantha_house < Peter_house)
    
    if s.check() == sat:
        m = s.model()
        # Create arrays to store results for each house
        names = [None] * 6
        children = [None] * 6
        
        # Assign names to houses
        names[m[Eric_house].as_long()] = "Eric"
        names[m[Alice_house].as_long()] = "Alice"
        names[m[Peter_house].as_long()] = "Peter"
        names[m[Bob_house].as_long()] = "Bob"
        names[m[Arnold_house].as_long()] = "Arnold"
        
        # Assign children to houses
        children[m[Timothy_house].as_long()] = "Timothy"
        children[m[Meredith_house].as_long()] = "Meredith"
        children[m[Samantha_house].as_long()] = "Samantha"
        children[m[Fred_house].as_long()] = "Fred"
        children[m[Bella_house].as_long()] = "Bella"
        
        # Build the output JSON
        rows = []
        for i in range(1, 6):
            rows.append([str(i), names[i], children[i]])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Children"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()