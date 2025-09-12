import json
from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define attributes and mappings
    names = ['Arnold', 'Peter', 'Eric']
    animals = ['bird', 'horse', 'cat']
    birthdays = ['jan', 'sept', 'april']
    hobbies = ['photography', 'cooking', 'gardening']
    drinks = ['milk', 'water', 'tea']
    hair_colors = ['black', 'brown', 'blonde']
    
    # Create variables for each house (0-indexed: house0=1, house1=2, house2=3)
    name = [Int(f'name_{i}') for i in range(3)]
    animal = [Int(f'animal_{i}') for i in range(3)]
    birthday = [Int(f'birthday_{i}') for i in range(3)]
    hobby = [Int(f'hobby_{i}') for i in range(3)]
    drink = [Int(f'drink_{i}') for i in range(3)]
    hair_color = [Int(f'hair_color_{i}') for i in range(3)]
    
    # Add constraints: all attributes must be between 0 and 2
    for i in range(3):
        s.add(name[i] >= 0, name[i] < 3)
        s.add(animal[i] >= 0, animal[i] < 3)
        s.add(birthday[i] >= 0, birthday[i] < 3)
        s.add(hobby[i] >= 0, hobby[i] < 3)
        s.add(drink[i] >= 0, drink[i] < 3)
        s.add(hair_color[i] >= 0, hair_color[i] < 3)
    
    # All attributes must be distinct
    s.add(Distinct(name))
    s.add(Distinct(animal))
    s.add(Distinct(birthday))
    s.add(Distinct(hobby))
    s.add(Distinct(drink))
    s.add(Distinct(hair_color))
    
    # Clue 1: Brown hair person loves cooking
    for i in range(3):
        s.add(Implies(hair_color[i] == 1, hobby[i] == 1))
    
    # Clue 2: April birthday in third house
    s.add(birthday[2] == 2)  # april is index 2
    
    # Clue 3: Eric not in first house
    s.add(name[0] != 2)  # Eric is index 2
    
    # Clue 4: Cat lover in second house
    s.add(animal[1] == 2)  # cat is index 2
    
    # Clue 5: Blonde hair left of milk drinker
    s.add(Exists([i, j], And(i < j, hair_color[i] == 2, drink[j] == 0)))
    
    # Clue 6: Gardening enthusiast likes milk
    for i in range(3):
        s.add(Implies(hobby[i] == 2, drink[i] == 0))
    
    # Clue 7: Cat lover has brown hair
    for i in range(3):
        s.add(Implies(animal[i] == 2, hair_color[i] == 1))
    
    # Clue 8: Arnold is bird keeper
    for i in range(3):
        s.add(Implies(name[i] == 0, animal[i] == 0))
    
    # Clue 9: Water drinker is photography enthusiast
    for i in range(3):
        s.add(Implies(drink[i] == 1, hobby[i] == 0))
    
    # Clue 10: September birthday directly left of Arnold
    s.add(Or(
        And(birthday[0] == 1, name[1] == 0),
        And(birthday[1] == 1, name[2] == 0)
    ))
    
    # Check and get solution
    if s.check() == sat:
        m = s.model()
        
        # Map integer values to strings
        solution_rows = []
        for i in range(3):
            house_num = str(i+1)
            n_val = m.eval(name[i]).as_long()
            a_val = m.eval(animal[i]).as_long()
            b_val = m.eval(birthday[i]).as_long()
            h_val = m.eval(hobby[i]).as_long()
            d_val = m.eval(drink[i]).as_long()
            hc_val = m.eval(hair_color[i]).as_long()
            
            row = [
                house_num,
                names[n_val],
                animals[a_val],
                birthdays[b_val],
                hobbies[h_val],
                drinks[d_val],
                hair_colors[hc_val]
            ]
            solution_rows.append(row)
        
        # Create JSON output
        output = {
            "solution": {
                "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
                "rows": solution_rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()