import json
from z3 import *

def main():
    # Define the categories and their constants
    Name, (Arnold, Peter, Eric) = EnumSort('Name', ['Arnold','Peter','Eric'])
    Animal, (bird, horse, cat) = EnumSort('Animal', ['bird','horse','cat'])
    Birthday, (jan, april, sept) = EnumSort('Birthday', ['jan','april','sept'])
    Hobby, (photography, cooking, gardening) = EnumSort('Hobby', ['photography','cooking','gardening'])
    Drink, (milk, water, tea) = EnumSort('Drink', ['milk','water','tea'])
    HairColor, (black, brown, blonde) = EnumSort('HairColor', ['black','brown','blonde'])
    
    # Create variables for each house (0,1,2) for each category
    n = [ Const('n0', Name), Const('n1', Name), Const('n2', Name) ]
    a = [ Const('a0', Animal), Const('a1', Animal), Const('a2', Animal) ]
    b = [ Const('b0', Birthday), Const('b1', Birthday), Const('b2', Birthday) ]
    h = [ Const('h0', Hobby), Const('h1', Hobby), Const('h2', Hobby) ]
    d = [ Const('d0', Drink), Const('d1', Drink), Const('d2', Drink) ]
    c = [ Const('c0', HairColor), Const('c1', HairColor), Const('c2', HairColor) ]
    
    s = Solver()
    
    # Distinct constraints for each category
    s.add(Distinct(n[0], n[1], n[2]))
    s.add(Distinct(a[0], a[1], a[2]))
    s.add(Distinct(b[0], b[1], b[2]))
    s.add(Distinct(h[0], h[1], h[2]))
    s.add(Distinct(d[0], d[1], d[2]))
    s.add(Distinct(c[0], c[1], c[2]))
    
    # Clue 1: The person who has brown hair is the person who loves cooking.
    for i in range(3):
        s.add( (c[i] == brown) == (h[i] == cooking) )
    
    # Clue 2: The person whose birthday is in April is in the third house.
    s.add( b[2] == april )
    
    # Clue 3: Eric is not in the first house.
    s.add( n[0] != Eric )
    
    # Clue 4: The cat lover is in the second house.
    s.add( a[1] == cat )
    
    # Clue 5: The person who has blonde hair is somewhere to the left of the person who likes milk.
    s.add( Or(
        And(c[0] == blonde, d[1] == milk),
        And(c[0] == blonde, d[2] == milk),
        And(c[1] == blonde, d[2] == milk)
    ))
    
    # Clue 6: The person who enjoys gardening is the person who likes milk.
    for i in range(3):
        s.add( (h[i] == gardening) == (d[i] == milk) )
    
    # Clue 7: The cat lover is the person who has brown hair.
    for i in range(3):
        s.add( (a[i] == cat) == (c[i] == brown) )
    
    # Clue 8: Arnold is the bird keeper.
    for i in range(3):
        s.add( (n[i] == Arnold) == (a[i] == bird) )
    
    # Clue 9: The one who only drinks water is the photography enthusiast.
    for i in range(3):
        s.add( (d[i] == water) == (h[i] == photography) )
    
    # Clue 10: The person whose birthday is in September is directly left of Arnold.
    s.add( Or(
        And(b[0] == sept, n[1] == Arnold),
        And(b[1] == sept, n[2] == Arnold)
    ))
    
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(3):
            row = [str(i+1)]
            row.append(str(m.eval(n[i])))
            row.append(str(m.eval(a[i])))
            row.append(str(m.eval(b[i])))
            row.append(str(m.eval(h[i])))
            row.append(str(m.eval(d[i])))
            row.append(str(m.eval(c[i])))
            rows.append(row)
        
        sol_dict = {
            "solution": {
                "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
                "rows": rows
            }
        }
        print(json.dumps(sol_dict))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()