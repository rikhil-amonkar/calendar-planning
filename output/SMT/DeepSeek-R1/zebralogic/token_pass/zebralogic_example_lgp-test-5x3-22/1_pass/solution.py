import json
from z3 import *

def main():
    s = Solver()
    
    # Define attributes and their possible values
    names = ['Arnold', 'Eric', 'Bob', 'Peter', 'Alice']
    smoothies = ['desert', 'watermelon', 'lime', 'cherry', 'dragonfruit']
    nationalities = ['german', 'swede', 'norwegian', 'dane', 'brit']
    
    # Create mappings from attribute values to integers
    name_to_int = {name: i for i, name in enumerate(names)}
    smoothie_to_int = {smoothie: i for i, smoothie in enumerate(smoothies)}
    nationality_to_int = {nationality: i for i, nationality in enumerate(nationalities)}
    
    # Create inverse mappings for output
    int_to_name = {i: name for name, i in name_to_int.items()}
    int_to_smoothie = {i: smoothie for smoothie, i in smoothie_to_int.items()}
    int_to_nationality = {i: nationality for nationality, i in nationality_to_int.items()}
    
    # Define variables for each house and attribute
    house_names = [Int(f'name_{i}') for i in range(5)]
    house_smoothies = [Int(f'smoothie_{i}') for i in range(5)]
    house_nationalities = [Int(f'nationality_{i}') for i in range(5)]
    
    # Add constraints for valid values
    for i in range(5):
        s.add(house_names[i] >= 0, house_names[i] < 5)
        s.add(house_smoothies[i] >= 0, house_smoothies[i] < 5)
        s.add(house_nationalities[i] >= 0, house_nationalities[i] < 5)
    
    # Each attribute must have unique values across houses
    s.add(Distinct(house_names))
    s.add(Distinct(house_smoothies))
    s.add(Distinct(house_nationalities))
    
    # Define clues
    # Clue 2: Dragonfruit smoothie in second house
    s.add(house_smoothies[1] == smoothie_to_int['dragonfruit'])
    
    # Clue 3: Peter not in first house
    s.add(house_names[0] != name_to_int['Peter'])
    
    # Clue 4: Dane and Brit adjacent
    dane = nationality_to_int['dane']
    brit = nationality_to_int['brit']
    adjacent_constraints = []
    for i in range(4):
        adjacent_constraints.append(And(
            house_nationalities[i] == dane,
            house_nationalities[i+1] == brit
        ))
        adjacent_constraints.append(And(
            house_nationalities[i] == brit,
            house_nationalities[i+1] == dane
        ))
    s.add(Or(adjacent_constraints))
    
    # Clue 5: Desert smoothie not in fifth house
    s.add(house_smoothies[4] != smoothie_to_int['desert'])
    
    # Clue 6: Swede left of Dragonfruit smoothie lover (already in house 2)
    s.add(house_nationalities[0] == nationality_to_int['swede'])
    
    # Clue 7: Two houses between Lime smoothie and Dane
    lime = smoothie_to_int['lime']
    for i in range(5):
        for j in range(5):
            if abs(i - j) == 3:
                s.add(Implies(
                    house_smoothies[i] == lime,
                    house_nationalities[j] == dane
                ))
                s.add(Implies(
                    house_nationalities[i] == dane,
                    house_smoothies[j] == lime
                ))
    
    # Clue 8: Bob is Dane
    for i in range(5):
        s.add(Implies(
            house_names[i] == name_to_int['Bob'],
            house_nationalities[i] == dane
        ))
    
    # Clue 9: Alice is Norwegian
    norwegian = nationality_to_int['norwegian']
    for i in range(5):
        s.add(Implies(
            house_names[i] == name_to_int['Alice'],
            house_nationalities[i] == norwegian
        ))
    
    # Clue 10: Alice in third house
    s.add(house_names[2] == name_to_int['Alice'])
    
    # Clue 11: Watermelon smoothie in third house
    s.add(house_smoothies[2] == smoothie_to_int['watermelon'])
    
    # Clue 1: Dragonfruit left of Eric (already satisfied by clue 2)
    # Since dragonfruit is in house 2, Eric must be in house 3,4, or5
    eric_houses = []
    for i in range(2,5):
        eric_houses.append(house_names[i] == name_to_int['Eric'])
    s.add(Or(eric_houses))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(5):
            name_val = m.evaluate(house_names[i]).as_long()
            smoothie_val = m.evaluate(house_smoothies[i]).as_long()
            nationality_val = m.evaluate(house_nationalities[i]).as_long()
            
            rows.append([
                str(i+1),
                int_to_name[name_val],
                int_to_smoothie[smoothie_val],
                int_to_nationality[nationality_val]
            ])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Nationality"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()