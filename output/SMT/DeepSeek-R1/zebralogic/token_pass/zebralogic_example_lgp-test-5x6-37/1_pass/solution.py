import json
from z3 import *

def main():
    # Define the attributes
    names = ['Bob', 'Arnold', 'Alice', 'Peter', 'Eric']
    hobbies = ['cooking', 'gardening', 'painting', 'photography', 'knitting']
    sports = ['swimming', 'tennis', 'soccer', 'baseball', 'basketball']
    styles = ['ranch', 'craftsman', 'victorian', 'modern', 'colonial']
    children = ['Timothy', 'Samantha', 'Bella', 'Meredith', 'Fred']
    heights = ['average', 'very tall', 'very short', 'short', 'tall']
    
    # Create Z3 enums for each attribute
    Name = Enum('Name', names)
    Hobby = Enum('Hobby', hobbies)
    Sport = Enum('Sport', sports)
    Style = Enum('Style', styles)
    Child = Enum('Child', children)
    Height = Enum('Height', heights)
    
    # Create variables for each house position (0-indexed)
    houses = [Int(f'house_{i}') for i in range(5)]
    solver = Solver()
    
    # Create attribute arrays for each house
    name_arr = [Const(f'name_{i}', Name) for i in range(5)]
    hobby_arr = [Const(f'hobby_{i}', Hobby) for i in range(5)]
    sport_arr = [Const(f'sport_{i}', Sport) for i in range(5)]
    style_arr = [Const(f'style_{i}', Style) for i in range(5)]
    child_arr = [Const(f'child_{i}', Child) for i in range(5)]
    height_arr = [Const(f'height_{i}', Height) for i in range(5)]
    
    # Add constraints that all attributes are distinct
    solver.add(Distinct(name_arr))
    solver.add(Distinct(hobby_arr))
    solver.add(Distinct(sport_arr))
    solver.add(Distinct(style_arr))
    solver.add(Distinct(child_arr))
    solver.add(Distinct(height_arr))
    
    # Each attribute must be one of its possible values
    for i in range(5):
        solver.add(Or([name_arr[i] == getattr(Name, n) for n in names]))
        solver.add(Or([hobby_arr[i] == getattr(Hobby, h) for h in hobbies]))
        solver.add(Or([sport_arr[i] == getattr(Sport, s) for s in sports]))
        solver.add(Or([style_arr[i] == getattr(Style, st) for st in styles]))
        solver.add(Or([child_arr[i] == getattr(Child, c) for c in children]))
        solver.add(Or([height_arr[i] == getattr(Height, ht) for ht in heights]))
    
    # Clue 1: The person who has an average height is the person's child is named Meredith.
    solver.add(Exists([i], And(i >= 0, i < 5, height_arr[i] == Height.average, child_arr[i] == Child.Meredith)))
    
    # Clue 2: The person who is tall is in the second house.
    solver.add(height_arr[1] == Height.tall)
    
    # Clue 3: Peter is directly left of the person residing in a Victorian house.
    for i in range(4):
        solver.add(Implies(name_arr[i] == Name.Peter, style_arr[i+1] == Style.victorian))
    
    # Clue 4: Alice is the person who is tall.
    solver.add(Exists([i], And(i >= 0, i < 5, name_arr[i] == Name.Alice, height_arr[i] == Height.tall)))
    
    # Clue 5: The person who loves baseball is the person who is very tall.
    solver.add(Exists([i], And(i >= 0, i < 5, sport_arr[i] == Sport.baseball, height_arr[i] == Height.very_tall)))
    
    # Clue 6: The person's child is named Meredith and the person who is the mother of Timothy are next to each other.
    mer_indices = [i for i in range(5) if child_arr[i] == Child.Meredith]
    tim_indices = [i for i in range(5) if child_arr[i] == Child.Timothy]
    solver.add(Or([Or(And(m == t-1), And(m == t+1)) for m in mer_indices for t in tim_indices]))
    
    # Clue 7: Bob is the person who paints as a hobby.
    solver.add(Exists([i], And(i >= 0, i < 5, name_arr[i] == Name.Bob, hobby_arr[i] == Hobby.painting)))
    
    # Clue 8: The person who enjoys gardening is in the second house.
    solver.add(hobby_arr[1] == Hobby.gardening)
    
    # Clue 9: The person who is very short is somewhere to the right of Eric.
    eric_index = [i for i in range(5) if name_arr[i] == Name.Eric]
    solver.add(Exists([i, j], And(i >= 0, i < 5, j >= 0, j < 5, name_arr[i] == Name.Eric, height_arr[j] == Height.very_short, j > i)))
    
    # Clue 10: The person who loves tennis is the person's child is named Samantha.
    solver.add(Exists([i], And(i >= 0, i < 5, sport_arr[i] == Sport.tennis, child_arr[i] == Child.Samantha)))
    
    # Clue 11: The person who loves soccer is not in the first house.
    solver.add(sport_arr[0] != Sport.soccer)
    
    # Clue 12: The person's child is named Samantha is the person in a modern-style house.
    solver.add(Exists([i], And(i >= 0, i < 5, child_arr[i] == Child.Samantha, style_arr[i] == Style.modern)))
    
    # Clue 13: The person in a Craftsman-style house is the person who has an average height.
    solver.add(Exists([i], And(i >= 0, i < 5, style_arr[i] == Style.craftsman, height_arr[i] == Height.average)))
    
    # Clue 14: The person's child is named Fred is the person residing in a Victorian house.
    solver.add(Exists([i], And(i >= 0, i < 5, child_arr[i] == Child.Fred, style_arr[i] == Style.victorian)))
    
    # Clue 15: The person who is short is the person who loves basketball.
    solver.add(Exists([i], And(i >= 0, i < 5, height_arr[i] == Height.short, sport_arr[i] == Sport.basketball)))
    
    # Clue 16: Peter is the person who is very tall.
    solver.add(Exists([i], And(i >= 0, i < 5, name_arr[i] == Name.Peter, height_arr[i] == Height.very_tall)))
    
    # Clue 17: The person in a ranch-style home is somewhere to the left of the person who loves cooking.
    ranch_indices = [i for i in range(5) if style_arr[i] == Style.ranch]
    cook_indices = [i for i in range(5) if hobby_arr[i] == Hobby.cooking]
    solver.add(Or([And(r < c) for r in ranch_indices for c in cook_indices]))
    
    # Clue 18: The person who enjoys knitting and the person who enjoys gardening are next to each other.
    knit_indices = [i for i in range(5) if hobby_arr[i] == Hobby.knitting]
    garden_indices = [i for i in range(5) if hobby_arr[i] == Hobby.gardening]
    solver.add(Or([Or(And(k == g-1), And(k == g+1)) for k in knit_indices for g in garden_indices]))
    
    # Clue 19: The person in a modern-style house is the person who loves cooking.
    solver.add(Exists([i], And(i >= 0, i < 5, style_arr[i] == Style.modern, hobby_arr[i] == Hobby.cooking)))
    
    # Clue 20: The person residing in a Victorian house is in the fifth house.
    solver.add(style_arr[4] == Style.victorian)
    
    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare results
        rows = []
        for i in range(5):
            name_val = model.eval(name_arr[i])
            hobby_val = model.eval(hobby_arr[i])
            sport_val = model.eval(sport_arr[i])
            style_val = model.eval(style_arr[i])
            child_val = model.eval(child_arr[i])
            height_val = model.eval(height_arr[i])
            
            # Convert Z3 symbols to strings
            name_str = str(name_val).split('!')[0]
            hobby_str = str(hobby_val).split('!')[0]
            sport_str = str(sport_val).split('!')[0]
            style_str = str(style_val).split('!')[0]
            child_str = str(child_val).split('!')[0]
            height_str = str(height_val).split('!')[0]
            
            rows.append([str(i+1), name_str, hobby_str, sport_str, style_str, child_str, height_str])
        
        # Create JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()