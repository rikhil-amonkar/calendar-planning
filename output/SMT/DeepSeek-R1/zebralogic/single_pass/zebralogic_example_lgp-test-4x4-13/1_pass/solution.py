import json
from z3 import *

def main():
    # Define the enums
    Name, (Alice, Peter, Arnold, Eric) = EnumSort('Name', ['Alice', 'Peter', 'Arnold', 'Eric'])
    Cigar, (prince, dunhill, blue_master, pall_mall) = EnumSort('Cigar', ['prince', 'dunhill', 'blue master', 'pall mall'])
    Sport, (swimming, basketball, soccer, tennis) = EnumSort('Sport', ['swimming', 'basketball', 'soccer', 'tennis'])
    Drink, (coffee, water, milk, tea) = EnumSort('Drink', ['coffee', 'water', 'milk', 'tea'])
    
    # Attributes for each house (4 houses: 0-indexed for 1,2,3,4)
    names = [Const('name_%d' % i, Name) for i in range(4)]
    cigars = [Const('cigar_%d' % i, Cigar) for i in range(4)]
    sports = [Const('sport_%d' % i, Sport) for i in range(4)]
    drinks = [Const('drink_%d' % i, Drink) for i in range(4)]
    
    s = Solver()
    
    # All attributes are distinct per category
    s.add(Distinct(names))
    s.add(Distinct(cigars))
    s.add(Distinct(sports))
    s.add(Distinct(drinks))
    
    # Clue1: Peter is in the fourth house.
    s.add(names[3] == Peter)
    
    # Clue8: The person who loves basketball is in the third house.
    s.add(sports[2] == basketball)
    
    # Clue2: The tea drinker is the person who loves basketball -> so in house3 (index2) drink must be tea.
    s.add(drinks[2] == tea)
    
    # Clue4: The person who loves basketball is Eric -> so in house3 (index2) name must be Eric.
    s.add(names[2] == Eric)
    
    # Clue6: There are two houses between the one who only drinks water and Peter.
    # Peter is in house4 (index3). The water drinker must be in house1 (index0).
    s.add(drinks[0] == water)
    
    # Clue10: Peter is the person partial to Pall Mall.
    s.add(cigars[3] == pall_mall)
    
    # Clue3: Arnold is the person who smokes Blue Master.
    # We use equivalence: for each house, Arnold <=> blue_master
    for i in range(4):
        s.add( (names[i] == Arnold) == (cigars[i] == blue_master) )
    
    # Clue5: The person who loves tennis is the person who smokes Blue Master.
    # So if a house has blue_master cigar, then it must have tennis sport.
    for i in range(4):
        s.add(If(cigars[i] == blue_master, sports[i] == tennis, True))
    
    # Clue7: The coffee drinker is Arnold.
    # Equivalence: for each house, coffee <=> Arnold
    for i in range(4):
        s.add( (drinks[i] == coffee) == (names[i] == Arnold) )
    
    # Clue9: The Prince smoker is the person who loves soccer.
    # If a house has prince cigar, then it must have soccer sport.
    for i in range(4):
        s.add(If(cigars[i] == prince, sports[i] == soccer, True))
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        rows = []
        for i in range(4):
            house_num = str(i+1)
            n_val = model[names[i]]
            name_str = n_val.decl().name()
            c_val = model[cigars[i]]
            cigar_str = c_val.decl().name()
            s_val = model[sports[i]]
            sport_str = s_val.decl().name()
            d_val = model[drinks[i]]
            drink_str = d_val.decl().name()
            row = [house_num, name_str, cigar_str, sport_str, drink_str]
            rows.append(row)
        
        solution_dict = {
            "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
            "rows": rows
        }
        output = {"solution": solution_dict}
        print(json.dumps(output))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()