import json
from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define the attributes for each house (0-indexed for houses 1-4)
    name = [Int('name_%d' % i) for i in range(4)]
    cigar = [Int('cigar_%d' % i) for i in range(4)]
    sport = [Int('sport_%d' % i) for i in range(4)]
    drink = [Int('drink_%d' % i) for i in range(4)]
    
    # Domain constraints
    for i in range(4):
        s.add(name[i] >= 0, name[i] < 4)
        s.add(cigar[i] >= 0, cigar[i] < 4)
        s.add(sport[i] >= 0, sport[i] < 4)
        s.add(drink[i] >= 0, drink[i] < 4)
    
    # Distinct constraints
    s.add(Distinct(name))
    s.add(Distinct(cigar))
    s.add(Distinct(sport))
    s.add(Distinct(drink))
    
    # Clue 1: Peter is in the fourth house.
    s.add(name[3] == 1)  # Peter=1
    
    # Clue 2: The tea drinker is the person who loves basketball.
    for i in range(4):
        s.add(Implies(drink[i] == 3, sport[i] == 1))
        s.add(Implies(sport[i] == 1, drink[i] == 3))
    
    # Clue 3: Arnold is the person who smokes Blue Master.
    for i in range(4):
        s.add(Implies(name[i] == 2, cigar[i] == 2))  # Arnold=2, Blue Master=2
        s.add(Implies(cigar[i] == 2, name[i] == 2))
    
    # Clue 4: The person who loves basketball is Eric.
    for i in range(4):
        s.add(Implies(sport[i] == 1, name[i] == 3))  # basketball=1, Eric=3
        s.add(Implies(name[i] == 3, sport[i] == 1))
    
    # Clue 5: The person who loves tennis is the person who smokes Blue Master.
    for i in range(4):
        s.add(Implies(sport[i] == 3, cigar[i] == 2))  # tennis=3, Blue Master=2
        s.add(Implies(cigar[i] == 2, sport[i] == 3))
    
    # Clue 6: Two houses between water drinker and Peter
    s.add(drink[0] == 1)  # water=1 in house1 (index0)
    
    # Clue 7: The coffee drinker is Arnold.
    for i in range(4):
        s.add(Implies(drink[i] == 0, name[i] == 2))  # coffee=0, Arnold=2
        s.add(Implies(name[i] == 2, drink[i] == 0))
    
    # Clue 8: The person who loves basketball is in the third house.
    s.add(sport[2] == 1)  # basketball=1 in house3 (index2)
    
    # Clue 9: The Prince smoker is the person who loves soccer.
    for i in range(4):
        s.add(Implies(cigar[i] == 0, sport[i] == 2))  # prince=0, soccer=2
        s.add(Implies(sport[i] == 2, cigar[i] == 0))
    
    # Clue 10: Peter is the person partial to Pall Mall.
    for i in range(4):
        s.add(Implies(name[i] == 1, cigar[i] == 3))  # Peter=1, Pall Mall=3
        s.add(Implies(cigar[i] == 3, name[i] == 1))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        
        # Map integer values to strings
        name_str = ['Alice', 'Peter', 'Arnold', 'Eric']
        cigar_str = ['prince', 'dunhill', 'blue master', 'pall mall']
        sport_str = ['swimming', 'basketball', 'soccer', 'tennis']
        drink_str = ['coffee', 'water', 'milk', 'tea']
        
        # Prepare results
        rows = []
        for i in range(4):
            n_val = m.evaluate(name[i]).as_long()
            c_val = m.evaluate(cigar[i]).as_long()
            s_val = m.evaluate(sport[i]).as_long()
            d_val = m.evaluate(drink[i]).as_long()
            
            row = [
                str(i+1),
                name_str[n_val],
                cigar_str[c_val],
                sport_str[s_val],
                drink_str[d_val]
            ]
            rows.append(row)
        
        # Create solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
                "rows": rows
            }
        }
        
        # Output JSON
        print(json.dumps(solution_dict, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()