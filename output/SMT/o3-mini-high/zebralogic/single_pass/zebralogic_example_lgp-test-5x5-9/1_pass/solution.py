from z3 import *
import json

def main():
    s = Solver()
    n = 5
    
    # Create an array of Int variables for each category for each house (houses are 0-indexed: 0 = House1, …, 4 = House5)
    names   = [Int(f"name_{i}") for i in range(n)]   # 0:"Bob", 1:"Arnold", 2:"Peter", 3:"Alice", 4:"Eric"
    drinks  = [Int(f"drink_{i}") for i in range(n)]  # 0:"milk", 1:"root beer", 2:"coffee", 3:"tea", 4:"water"
    colors  = [Int(f"color_{i}") for i in range(n)]  # 0:"blue", 1:"green", 2:"white", 3:"yellow", 4:"red"
    flowers = [Int(f"flower_{i}") for i in range(n)] # 0:"daffodils", 1:"roses", 2:"lilies", 3:"tulips", 4:"carnations"
    hobbies = [Int(f"hobby_{i}") for i in range(n)]  # 0:"painting", 1:"cooking", 2:"photography", 3:"gardening", 4:"knitting"
    
    # Each variable is in the domain 0..4 and all values are distinct per category.
    for i in range(n):
        s.add(And(names[i] >= 0, names[i] < n))
        s.add(And(drinks[i] >= 0, drinks[i] < n))
        s.add(And(colors[i] >= 0, colors[i] < n))
        s.add(And(flowers[i] >= 0, flowers[i] < n))
        s.add(And(hobbies[i] >= 0, hobbies[i] < n))
    
    s.add(Distinct(names))
    s.add(Distinct(drinks))
    s.add(Distinct(colors))
    s.add(Distinct(flowers))
    s.add(Distinct(hobbies))
    
    # ----- Clues as constraints -----
    
    # Clue 1: Alice is not in the fourth house (House4 is index 3). 
    # (In our names mapping, Alice = 3.)
    s.add(names[3] != 3)
    
    # Clue 8 & 13: The one who drinks water is Peter and is in the third house (House3 is index 2).
    # In drinks mapping: water = 4; in names mapping: Peter = 2.
    s.add(drinks[2] == 4)
    s.add(names[2] == 2)
    
    # Clue 15: The person who loves white is in the second house (House2 is index 1).
    # In colors mapping: white = 2.
    s.add(colors[1] == 2)
    
    # Clue 7: Eric is directly left of the tea drinker.
    # In names mapping, Eric = 4 and in drinks mapping, tea = 3.
    s.add(Or(And(names[0] == 4, drinks[1] == 3),
             And(names[1] == 4, drinks[2] == 3),
             And(names[2] == 4, drinks[3] == 3),
             And(names[3] == 4, drinks[4] == 3)))
    
    # Triple A (Clues 2 & 14):
    # "The root beer lover is the person who enjoys gardening" and "loves a carnations arrangement."
    # In drinks: root beer = 1, in flowers: carnations = 4, in hobbies: gardening = 3.
    for i in range(n):
        s.add(Implies(drinks[i] == 1, And(flowers[i] == 4, hobbies[i] == 3)))
        s.add(Implies(And(flowers[i] == 4, hobbies[i] == 3), drinks[i] == 1))
    
    # Triple B (Clues 3 & 4):
    # "The person whose favorite color is green is the coffee drinker and loves a bouquet of lilies."
    # In colors: green = 1, drinks: coffee = 2, flowers: lilies = 2.
    for i in range(n):
        s.add(Implies(colors[i] == 1, And(drinks[i] == 2, flowers[i] == 2)))
        s.add(Implies(And(drinks[i] == 2, flowers[i] == 2), colors[i] == 1))
    
    # Triple C (Clue 6):
    # "The person who loves cooking is the person who loves blue."
    # In hobbies: cooking = 1 and in colors: blue = 0.
    for i in range(n):
        s.add(Implies(hobbies[i] == 1, colors[i] == 0))
        s.add(Implies(colors[i] == 0, hobbies[i] == 1))
    
    # Clue 9: Arnold is the photography enthusiast.
    # In names: Arnold = 1, in hobbies: photography = 2.
    for i in range(n):
        s.add(Implies(names[i] == 1, hobbies[i] == 2))
    
    # Clue 10: The person who loves white is the person who loves the rose bouquet.
    # In colors: white = 2, in flowers: roses = 1.
    for i in range(n):
        s.add(Implies(colors[i] == 2, flowers[i] == 1))
        s.add(Implies(flowers[i] == 1, colors[i] == 2))
    
    # Clue 11: There is one house between the person who loves carnations and the person whose favorite color is red.
    # In flowers: carnations = 4, in colors: red = 4.
    for i in range(n):
        for j in range(n):
            s.add(Implies(And(flowers[i] == 4, colors[j] == 4), Or(j == i + 2, j == i - 2)))
    
    # Clue 12: The person who loves cooking is somewhere to the left of the person who paints.
    # In hobbies: cooking = 1, painting = 0.
    for i in range(n):
        for j in range(n):
            s.add(Implies(And(hobbies[i] == 1, hobbies[j] == 0), i < j))
    
    # (Clues 3,4, and 14 have already been handled in the above triple constraints.)
    
    # ----- End of Constraints -----
    
    if s.check() == sat:
        m = s.model()
        
        # Define mapping dictionaries to convert from our integer codes to strings:
        names_map   = {0: "Bob", 1: "Arnold", 2: "Peter", 3: "Alice", 4: "Eric"}
        drinks_map  = {0: "milk", 1: "root beer", 2: "coffee", 3: "tea", 4: "water"}
        colors_map  = {0: "blue", 1: "green", 2: "white", 3: "yellow", 4: "red"}
        flowers_map = {0: "daffodils", 1: "roses", 2: "lilies", 3: "tulips", 4: "carnations"}
        hobbies_map = {0: "painting", 1: "cooking", 2: "photography", 3: "gardening", 4: "knitting"}
        
        result_rows = []
        for i in range(n):
            house_number = str(i + 1)
            name_val   = m[names[i]].as_long()
            drink_val  = m[drinks[i]].as_long()
            color_val  = m[colors[i]].as_long()
            flower_val = m[flowers[i]].as_long()
            hobby_val  = m[hobbies[i]].as_long()
            row = [
                house_number,
                names_map[name_val],
                drinks_map[drink_val],
                colors_map[color_val],
                flowers_map[flower_val],
                hobbies_map[hobby_val]
            ]
            result_rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
                "rows": result_rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()