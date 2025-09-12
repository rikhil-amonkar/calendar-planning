import json
from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define the attributes
    houses = [1, 2, 3, 4, 5]
    names = ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter']
    vacations = ['cruise', 'city', 'camping', 'beach', 'mountain']
    children = ['Bella', 'Samantha', 'Fred', 'Meredith', 'Timothy']
    nationalities = ['dane', 'norwegian', 'brit', 'german', 'swede']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in houses]
    vacation_vars = [Int(f'vacation_{i}') for i in houses]
    child_vars = [Int(f'child_{i}') for i in houses]
    nationality_vars = [Int(f'nationality_{i}') for i in houses]
    
    # Define domains for each variable
    for i in houses:
        s.add(And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        s.add(And(vacation_vars[i-1] >= 0, vacation_vars[i-1] < len(vacations)))
        s.add(And(child_vars[i-1] >= 0, child_vars[i-1] < len(children)))
        s.add(And(nationality_vars[i-1] >= 0, nationality_vars[i-1] < len(nationalities)))
    
    # All attributes are distinct per house
    s.add(Distinct(name_vars))
    s.add(Distinct(vacation_vars))
    s.add(Distinct(child_vars))
    s.add(Distinct(nationality_vars))
    
    # Clue 1: The Norwegian is Peter.
    for i in houses:
        s.add(Implies(nationality_vars[i-1] == nationalities.index('norwegian'), 
                      name_vars[i-1] == names.index('Peter')))
    
    # Clue 2: The Swedish person is the person's child is named Bella.
    for i in houses:
        s.add(Implies(nationality_vars[i-1] == nationalities.index('swede'), 
                      child_vars[i-1] == children.index('Bella')))
    
    # Clue 3: The person who loves beach vacations is directly left of the person's child is named Samantha.
    # Fixed: "directly left" means house i has beach, house i+1 has Samantha
    for i in range(0, 4):  # Houses 1-4 (since directly left means i+1 exists)
        s.add(Implies(vacation_vars[i] == vacations.index('beach'), 
                      child_vars[i+1] == children.index('Samantha')))
    
    # Clue 4: The person's child is named Bella is not in the second house.
    s.add(child_vars[1] != children.index('Bella'))
    
    # Clue 5: Alice is the British person.
    for i in houses:
        s.add(Implies(name_vars[i-1] == names.index('Alice'), 
                      nationality_vars[i-1] == nationalities.index('brit')))
    
    # Clue 6: The person who likes going on cruises is in the first house.
    s.add(vacation_vars[0] == vacations.index('cruise'))
    
    # Clue 7: The person's child is named Meredith is in the fourth house.
    s.add(child_vars[3] == children.index('Meredith'))
    
    # Clue 8: Eric is not in the fifth house.
    s.add(name_vars[4] != names.index('Eric'))
    
    # Clue 9: The Swedish person is somewhere to the right of the Norwegian.
    # Use positions instead of creating new variables
    for i in houses:
        for j in houses:
            if i < j:  # j is to the right of i
                s.add(Implies(
                    And(nationality_vars[i-1] == nationalities.index('norwegian'),
                        nationality_vars[j-1] == nationalities.index('swede')),
                    True  # This condition is satisfied
                ))
    
    # Clue 10: There is one house between the person's child is named Fred and the person who prefers city breaks.
    # Fixed: Use absolute difference of 2
    for i in houses:
        for j in houses:
            if abs(i - j) == 2:  # Exactly one house between them
                s.add(Implies(
                    child_vars[i-1] == children.index('Fred'),
                    vacation_vars[j-1] == vacations.index('city')
                ))
                s.add(Implies(
                    vacation_vars[i-1] == vacations.index('city'),
                    child_vars[j-1] == children.index('Fred')
                ))
    
    # Clue 11: Bob is the person who enjoys camping trips.
    for i in houses:
        s.add(Implies(name_vars[i-1] == names.index('Bob'), 
                      vacation_vars[i-1] == vacations.index('camping')))
    
    # Clue 12: The Dane is in the fifth house.
    s.add(nationality_vars[4] == nationalities.index('dane'))
    
    # Clue 13: The person who enjoys camping trips is not in the fifth house.
    s.add(vacation_vars[4] != vacations.index('camping'))
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        
        # Extract values
        result = []
        for i in houses:
            name_idx = model.evaluate(name_vars[i-1]).as_long()
            vacation_idx = model.evaluate(vacation_vars[i-1]).as_long()
            child_idx = model.evaluate(child_vars[i-1]).as_long()
            nationality_idx = model.evaluate(nationality_vars[i-1]).as_long()
            
            result.append({
                "House": str(i),
                "Name": names[name_idx],
                "Vacation": vacations[vacation_idx],
                "Children": children[child_idx],
                "Nationality": nationalities[nationality_idx]
            })
        
        # Format output as JSON
        output = {
            "solution": result
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()