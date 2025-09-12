import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define houses
    houses = [0, 1, 2, 3]  # Changed to 0-indexed
    
    # Define attributes
    names = ['Arnold', 'Peter', 'Eric', 'Alice']
    styles = ['craftsman', 'colonial', 'victorian', 'ranch']
    hair_colors = ['red', 'blonde', 'black', 'brown']
    children = ['Bella', 'Fred', 'Meredith', 'Samantha']
    book_genres = ['mystery', 'fantasy', 'romance', 'science fiction']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{h}') for h in range(4)]
    style_vars = [Int(f'style_{h}') for h in range(4)]
    hair_vars = [Int(f'hair_{h}') for h in range(4)]
    child_vars = [Int(f'child_{h}') for h in range(4)]
    book_vars = [Int(f'book_{h}') for h in range(4)]
    
    # Constraint: all attributes must be within valid range (0-3)
    for h in range(4):
        solver.add(And(name_vars[h] >= 0, name_vars[h] < 4))
        solver.add(And(style_vars[h] >= 0, style_vars[h] < 4))
        solver.add(And(hair_vars[h] >= 0, hair_vars[h] < 4))
        solver.add(And(child_vars[h] >= 0, child_vars[h] < 4))
        solver.add(And(book_vars[h] >= 0, book_vars[h] < 4))
    
    # Constraint: all attributes are distinct within their category
    solver.add(Distinct(name_vars))
    solver.add(Distinct(style_vars))
    solver.add(Distinct(hair_vars))
    solver.add(Distinct(child_vars))
    solver.add(Distinct(book_vars))
    
    # Get indices for easier reference
    arnold_idx = names.index('Arnold')
    peter_idx = names.index('Peter')
    eric_idx = names.index('Eric')
    alice_idx = names.index('Alice')
    
    craftsman_idx = styles.index('craftsman')
    colonial_idx = styles.index('colonial')
    victorian_idx = styles.index('victorian')
    ranch_idx = styles.index('ranch')
    
    red_idx = hair_colors.index('red')
    blonde_idx = hair_colors.index('blonde')
    black_idx = hair_colors.index('black')
    brown_idx = hair_colors.index('brown')
    
    bella_idx = children.index('Bella')
    fred_idx = children.index('Fred')
    meredith_idx = children.index('Meredith')
    samantha_idx = children.index('Samantha')
    
    mystery_idx = book_genres.index('mystery')
    fantasy_idx = book_genres.index('fantasy')
    romance_idx = book_genres.index('romance')
    scifi_idx = book_genres.index('science fiction')
    
    # Clue 1: The person in a Craftsman-style house is in the third house.
    solver.add(style_vars[2] == craftsman_idx)  # House 3 is index 2
    
    # Clue 2: Alice is the person who loves romance books.
    # Instead of Exists, add constraint that for some house, name is Alice and book is romance
    solver.add(Or([And(name_vars[h] == alice_idx, book_vars[h] == romance_idx) for h in range(4)]))
    
    # Clue 3: The person who has brown hair is in the fourth house.
    solver.add(hair_vars[3] == brown_idx)  # House 4 is index 3
    
    # Clue 4: The person's child is named Samantha is in the fourth house.
    solver.add(child_vars[3] == samantha_idx)  # House 4 is index 3
    
    # Clue 5: The person in a ranch-style home is somewhere to the right of the person who has red hair.
    # Create position variables
    red_house = Int('red_house')
    ranch_house = Int('ranch_house')
    solver.add(red_house >= 1, red_house <= 4)
    solver.add(ranch_house >= 1, ranch_house <= 4)
    solver.add(ranch_house > red_house)
    
    # Link position variables to actual attributes
    for h in range(4):
        solver.add(Implies(hair_vars[h] == red_idx, red_house == h+1))
        solver.add(Implies(style_vars[h] == ranch_idx, ranch_house == h+1))
    
    # Clue 6: Peter is the person's child is named Bella.
    solver.add(Or([And(name_vars[h] == peter_idx, child_vars[h] == bella_idx) for h in range(4)]))
    
    # Clue 7: Arnold is the person who has red hair.
    solver.add(Or([And(name_vars[h] == arnold_idx, hair_vars[h] == red_idx) for h in range(4)]))
    
    # Clue 8: Alice is the person living in a colonial-style house.
    solver.add(Or([And(name_vars[h] == alice_idx, style_vars[h] == colonial_idx) for h in range(4)]))
    
    # Clue 9: The person who has black hair is in the second house.
    solver.add(hair_vars[1] == black_idx)  # House 2 is index 1
    
    # Clue 10: The person who loves fantasy books is Peter.
    solver.add(Or([And(name_vars[h] == peter_idx, book_vars[h] == fantasy_idx) for h in range(4)]))
    
    # Clue 11: Arnold is the person's child is named Meredith.
    solver.add(Or([And(name_vars[h] == arnold_idx, child_vars[h] == meredith_idx) for h in range(4)]))
    
    # Clue 12: The person who has black hair is Eric.
    solver.add(Or([And(name_vars[h] == eric_idx, hair_vars[h] == black_idx) for h in range(4)]))
    
    # Clue 13: The person who loves science fiction books is Arnold.
    solver.add(Or([And(name_vars[h] == arnold_idx, book_vars[h] == scifi_idx) for h in range(4)]))
    
    # Check if solution exists
    if solver.check() == sat:
        model = solver.model()
        
        # Extract solution
        solution = []
        for house in range(4):
            name_idx = model.evaluate(name_vars[house]).as_long()
            style_idx = model.evaluate(style_vars[house]).as_long()
            hair_idx = model.evaluate(hair_vars[house]).as_long()
            child_idx = model.evaluate(child_vars[house]).as_long()
            book_idx = model.evaluate(book_vars[house]).as_long()
            
            row = [
                str(house + 1),  # Convert back to 1-indexed for display
                names[name_idx],
                styles[style_idx],
                hair_colors[hair_idx],
                children[child_idx],
                book_genres[book_idx]
            ]
            solution.append(row)
        
        # Format output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
                "rows": solution
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()