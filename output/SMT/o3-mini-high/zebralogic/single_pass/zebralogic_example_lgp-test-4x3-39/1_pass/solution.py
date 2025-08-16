from z3 import *
import json

def main():
    s = Solver()

    # Define integer variables for the positions (house numbers 1 to 4) for each attribute.
    # Names:
    Eric = Int('Eric')
    Alice = Int('Alice')
    Peter = Int('Peter')
    Arnold = Int('Arnold')
    
    # Hair colors:
    blonde = Int('blonde')
    black = Int('black')
    red = Int('red')
    brown = Int('brown')
    
    # Favorite sports:
    swimming = Int('swimming')
    soccer = Int('soccer')
    basketball = Int('basketball')
    tennis = Int('tennis')
    
    # All variables must be in the range 1 to 4
    variables = [Eric, Alice, Peter, Arnold, blonde, black, red, brown, swimming, soccer, basketball, tennis]
    for var in variables:
        s.add(And(var >= 1, var <= 4))
    
    # Each set of attributes must be all assigned to different houses.
    s.add(Distinct(Eric, Alice, Peter, Arnold))
    s.add(Distinct(blonde, black, red, brown))
    s.add(Distinct(swimming, soccer, basketball, tennis))
    
    # Now add the clues:
    # Clue 2: Eric is the person who has blonde hair.
    s.add(Eric == blonde)
    
    # Clue 1: The person who loves soccer is not in the second house.
    s.add(soccer != 2)
    
    # Clue 3: The person who has blonde hair is somewhere to the right of the person who loves basketball.
    s.add(blonde > basketball)
    
    # Clue 4: The person who has black hair is the person who loves tennis.
    s.add(black == tennis)
    
    # Clue 5: Arnold is somewhere to the left of the person who has red hair.
    s.add(Arnold < red)
    
    # Clue 6: Alice is the person who loves swimming.
    s.add(Alice == swimming)
    
    # Clue 7: The person who has red hair is directly left of the person who has black hair.
    s.add(red + 1 == black)
    
    if s.check() == sat:
        m = s.model()
        # Create a dictionary to keep each house's attributes.
        houses_info = {i: {} for i in range(1, 5)}
        
        # Map names to houses.
        for name, var in [("Eric", Eric), ("Alice", Alice), ("Peter", Peter), ("Arnold", Arnold)]:
            pos = m.evaluate(var).as_long()
            houses_info[pos]["Name"] = name
            
        # Map hair colors to houses.
        for hair, var in [("blonde", blonde), ("black", black), ("red", red), ("brown", brown)]:
            pos = m.evaluate(var).as_long()
            houses_info[pos]["HairColor"] = hair
            
        # Map favorite sports to houses.
        for sport, var in [("swimming", swimming), ("soccer", soccer), ("basketball", basketball), ("tennis", tennis)]:
            pos = m.evaluate(var).as_long()
            houses_info[pos]["FavoriteSport"] = sport
            
        # Build the rows list in the order of houses 1 to 4.
        rows = []
        for i in range(1, 5):
            row = [str(i), houses_info[i]["Name"], houses_info[i]["HairColor"], houses_info[i]["FavoriteSport"]]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport"],
                "rows": rows
            }
        }
        print(json.dumps(solution))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()