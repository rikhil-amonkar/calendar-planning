import json
from z3 import *

def main():
    # Define the attributes and their possible values
    Name = Enum('Name', ['Arnold', 'Eric'])
    HairColor = Enum('HairColor', ['black', 'brown'])
    FavoriteSport = Enum('FavoriteSport', ['basketball', 'soccer'])
    Smoothie = Enum('Smoothie', ['desert', 'cherry'])
    
    # Create variables for each house
    houses = [1, 2]
    names = [Const(f'name_{i}', Name) for i in houses]
    hairs = [Const(f'hair_{i}', HairColor) for i in houses]
    sports = [Const(f'sport_{i}', FavoriteSport) for i in houses]
    smoothies = [Const(f'smoothie_{i}', Smoothie) for i in houses]
    
    s = Solver()
    
    # Each attribute must be unique across houses
    s.add(Distinct(names))
    s.add(Distinct(hairs))
    s.add(Distinct(sports))
    s.add(Distinct(smoothies))
    
    # Clue 1: The Desert smoothie lover is Arnold.
    for i in range(len(houses)):
        s.add(Implies(smoothies[i] == Smoothie.desert, names[i] == Name.Arnold))
    
    # Clue 2: The person with brown hair loves basketball.
    for i in range(len(houses)):
        s.add(Implies(hairs[i] == HairColor.brown, sports[i] == FavoriteSport.basketball))
        s.add(Implies(sports[i] == FavoriteSport.basketball, hairs[i] == HairColor.brown))
    
    # Clue 3: Arnold is left of the black-haired person
    # Since only 2 houses, Arnold must be in house 1, black hair in house 2
    s.add(names[0] == Name.Arnold)
    s.add(hairs[1] == HairColor.black)
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        
        # Mapping from Z3 values to strings
        name_map = {Name.Arnold: "Arnold", Name.Eric: "Eric"}
        hair_map = {HairColor.black: "black", HairColor.brown: "brown"}
        sport_map = {FavoriteSport.basketball: "basketball", FavoriteSport.soccer: "soccer"}
        smoothie_map = {Smoothie.desert: "desert", Smoothie.cherry: "cherry"}
        
        rows = []
        for i in range(len(houses)):
            n_val = m.evaluate(names[i])
            h_val = m.evaluate(hairs[i])
            sp_val = m.evaluate(sports[i])
            sm_val = m.evaluate(smoothies[i])
            
            row = [
                str(i+1),
                name_map[n_val],
                hair_map[h_val],
                sport_map[sp_val],
                smoothie_map[sm_val]
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
                "rows": rows
            }
        }
        
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()