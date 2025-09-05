from z3 import *
import json

def main():
    # Define the attributes using EnumSort
    NameSort, (Arnold, Eric) = EnumSort('Name', ['Arnold', 'Eric'])
    HairSort, (black, brown) = EnumSort('Hair', ['black', 'brown'])
    SportSort, (basketball, soccer) = EnumSort('Sport', ['basketball', 'soccer'])
    SmoothieSort, (desert, cherry) = EnumSort('Smoothie', ['desert', 'cherry'])
    
    # Create variables for each house and each attribute
    houses = [1, 2]
    name = [Const(f'name_{i}', NameSort) for i in houses]
    hair_color = [Const(f'hair_{i}', HairSort) for i in houses]
    sport = [Const(f'sport_{i}', SportSort) for i in houses]
    smoothie = [Const(f'smoothie_{i}', SmoothieSort) for i in houses]
    
    s = Solver()
    
    # Add uniqueness constraints for each attribute
    s.add(Distinct(name))
    s.add(Distinct(hair_color))
    s.add(Distinct(sport))
    s.add(Distinct(smoothie))
    
    # Clue 1: The Desert smoothie lover is Arnold.
    for i in houses:
        s.add(Implies(smoothie[i-1] == desert, name[i-1] == Arnold))
        s.add(Implies(name[i-1] == Arnold, smoothie[i-1] == desert))
    
    # Clue 2: The person with brown hair loves basketball.
    for i in houses:
        s.add(Implies(hair_color[i-1] == brown, sport[i-1] == basketball))
        s.add(Implies(sport[i-1] == basketball, hair_color[i-1] == brown))
    
    # Clue 3: Arnold is left of the person with black hair.
    # Since houses are ordered, Arnold must be in house 1 and black hair in house 2
    s.add(name[0] == Arnold)
    s.add(hair_color[1] == black)
    
    # Check satisfaction and get model
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(2):
            # Evaluate each attribute for the current house
            n_val = m.eval(name[i])
            h_val = m.eval(hair_color[i])
            sp_val = m.eval(sport[i])
            sm_val = m.eval(smoothie[i])
            
            # Convert Z3 values to strings
            n_str = 'Arnold' if n_val == Arnold else 'Eric'
            h_str = 'black' if h_val == black else 'brown'
            sp_str = 'basketball' if sp_val == basketball else 'soccer'
            sm_str = 'desert' if sm_val == desert else 'cherry'
            
            rows.append([str(i+1), n_str, h_str, sp_str, sm_str])
        
        # Create JSON output
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