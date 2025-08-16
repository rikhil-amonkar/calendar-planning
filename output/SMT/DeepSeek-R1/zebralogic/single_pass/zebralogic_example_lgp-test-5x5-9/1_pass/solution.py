from z3 import *

def main():
    # Define the enums and their constructors
    Name, (bob, arnold, peter, alice, eric) = EnumSort('Name', ['Bob','Arnold','Peter','Alice','Eric'])
    Drink, (milk, root_beer, coffee, tea, water) = EnumSort('Drink', ['milk','root beer','coffee','tea','water'])
    Color, (blue, green, white, yellow, red) = EnumSort('Color', ['blue','green','white','yellow','red'])
    Flower, (daffodils, roses, lilies, tulips, carnations) = EnumSort('Flower', ['daffodils','roses','lilies','tulips','carnations'])
    Hobby, (painting, cooking, photography, gardening, knitting) = EnumSort('Hobby', ['painting','cooking','photography','gardening','knitting'])
    
    # Lists of constructors and their string representations for each attribute
    name_constr = [bob, arnold, peter, alice, eric]
    name_strs = ['Bob','Arnold','Peter','Alice','Eric']
    
    drink_constr = [milk, root_beer, coffee, tea, water]
    drink_strs = ['milk','root beer','coffee','tea','water']
    
    color_constr = [blue, green, white, yellow, red]
    color_strs = ['blue','green','white','yellow','red']
    
    flower_constr = [daffodils, roses, lilies, tulips, carnations]
    flower_strs = ['daffodils','roses','lilies','tulips','carnations']
    
    hobby_constr = [painting, cooking, photography, gardening, knitting]
    hobby_strs = ['painting','cooking','photography','gardening','knitting']
    
    # Create attribute arrays for 5 houses
    names = [Const('name_%d' % i, Name) for i in range(5)]
    drinks = [Const('drink_%d' % i, Drink) for i in range(5)]
    colors = [Const('color_%d' % i, Color) for i in range(5)]
    flowers = [Const('flower_%d' % i, Flower) for i in range(5)]
    hobbies = [Const('hobby_%d' % i, Hobby) for i in range(5)]
    
    s = Solver()
    
    # All attributes must be distinct
    s.add(Distinct(names))
    s.add(Distinct(drinks))
    s.add(Distinct(colors))
    s.add(Distinct(flowers))
    s.add(Distinct(hobbies))
    
    # Clue 1: Alice is not in the fourth house (index 3)
    s.add(names[3] != alice)
    
    # Clue 2: Root beer lover is the gardener
    for i in range(5):
        s.add( (drinks[i] == root_beer) == (hobbies[i] == gardening) )
    
    # Clue 3: Green color is coffee drinker
    for i in range(5):
        s.add( (colors[i] == green) == (drinks[i] == coffee) )
    
    # Clue 4: Green color is lilies
    for i in range(5):
        s.add( (colors[i] == green) == (flowers[i] == lilies) )
    
    # Clue 5: Blue color is right of daffodils
    s.add(Or([And(flowers[i] == daffodils, colors[j] == blue) for i in range(5) for j in range(5) if j > i]))
    
    # Clue 6: Cooking hobby is blue color
    for i in range(5):
        s.add( (hobbies[i] == cooking) == (colors[i] == blue) )
    
    # Clue 7: Eric is directly left of the tea drinker
    s.add(Or([And(names[i] == eric, drinks[i+1] == tea) for i in range(4)]))
    
    # Clue 8: Water drinker is Peter
    for i in range(5):
        s.add( (drinks[i] == water) == (names[i] == peter) )
    
    # Clue 9: Arnold is photography enthusiast
    for i in range(5):
        s.add( (names[i] == arnold) == (hobbies[i] == photography) )
    
    # Clue 10: White color is roses
    for i in range(5):
        s.add( (colors[i] == white) == (flowers[i] == roses) )
    
    # Clue 11: One house between carnations and red color
    s.add(Or(
        Or([And(flowers[i] == carnations, colors[i+2] == red) for i in [0,1,2]]),
        Or([And(flowers[i] == carnations, colors[i-2] == red) for i in [2,3,4]])
    ))
    
    # Clue 12: Cooking is left of painting
    s.add(Or([And(hobbies[i] == cooking, hobbies[j] == painting) for i in range(5) for j in range(5) if i < j]))
    
    # Clue 13: Water drinker in third house (index 2)
    s.add(drinks[2] == water)
    
    # Clue 14: Carnations is root beer lover
    for i in range(5):
        s.add( (flowers[i] == carnations) == (drinks[i] == root_beer) )
    
    # Clue 15: White color in second house (index 1)
    s.add(colors[1] == white)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(5):
            n_val = m.evaluate(names[i])
            d_val = m.evaluate(drinks[i])
            c_val = m.evaluate(colors[i])
            f_val = m.evaluate(flowers[i])
            h_val = m.evaluate(hobbies[i])
            
            # Convert to strings
            n_str = None
            for idx, constr in enumerate(name_constr):
                if m.evaluate(n_val == constr):
                    n_str = name_strs[idx]
                    break
            d_str = None
            for idx, constr in enumerate(drink_constr):
                if m.evaluate(d_val == constr):
                    d_str = drink_strs[idx]
                    break
            c_str = None
            for idx, constr in enumerate(color_constr):
                if m.evaluate(c_val == constr):
                    c_str = color_strs[idx]
                    break
            f_str = None
            for idx, constr in enumerate(flower_constr):
                if m.evaluate(f_val == constr):
                    f_str = flower_strs[idx]
                    break
            h_str = None
            for idx, constr in enumerate(hobby_constr):
                if m.evaluate(h_val == constr):
                    h_str = hobby_strs[idx]
                    break
            
            rows.append([str(i+1), n_str, d_str, c_str, f_str, h_str])
        
        # Create the solution dictionary
        solution = {
            "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
            "rows": rows
        }
        
        # Output as JSON string
        import json
        json_output = json.dumps({"solution": solution}, indent=2)
        print(json_output)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()