import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define houses
    houses = [1, 2, 3, 4]
    
    # Define attributes
    names = ['Arnold', 'Peter', 'Eric', 'Alice']
    styles = ['craftsman', 'colonial', 'victorian', 'ranch']
    hair_colors = ['red', 'blonde', 'black', 'brown']
    children = ['Bella', 'Fred', 'Meredith', 'Samantha']
    book_genres = ['mystery', 'fantasy', 'romance', 'science fiction']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{h}') for h in houses]
    style_vars = [Int(f'style_{h}') for h in houses]
    hair_vars = [Int(f'hair_{h}') for h in houses]
    child_vars = [Int(f'child_{h}') for h in houses]
    book_vars = [Int(f'book_{h}') for h in houses]
    
    # Constraint: all attributes must be within valid range (0-3)
    for h in houses:
        solver.add(And(name_vars[h-1] >= 0, name_vars[h-1] < 4))
        solver.add(And(style_vars[h-1] >= 0, style_vars[h-1] < 4))
        solver.add(And(hair_vars[h-1] >= 0, hair_vars[h-1] < 4))
        solver.add(And(child_vars[h-1] >= 0, child_vars[h-1] < 4))
        solver.add(And(book_vars[h-1] >= 0, book_vars[h-1] < 4))
    
    # Constraint: all attributes are distinct within their category
    solver.add(Distinct(name_vars))
    solver.add(Distinct(style_vars))
    solver.add(Distinct(hair_vars))
    solver.add(Distinct(child_vars))
    solver.add(Distinct(book_vars))
    
    # Clue 1: The person in a Craftsman-style house is in the third house.
    craftsman_idx = styles.index('craftsman')
    solver.add(style_vars[2] == craftsman_idx)
    
    # Clue 2: Alice is the person who loves romance books.
    alice_idx = names.index('Alice')
    romance_idx = book_genres.index('romance')
    solver.add(Exists([h], And(h >= 0, h < 4, name_vars[h] == alice_idx, book_vars[h] == romance_idx)))
    
    # Clue 3: The person who has brown hair is in the fourth house.
    brown_idx = hair_colors.index('brown')
    solver.add(hair_vars[3] == brown_idx)
    
    # Clue 4: The person's child is named Samantha is in the fourth house.
    samantha_idx = children.index('Samantha')
    solver.add(child_vars[3] == samantha_idx)
    
    # Clue 5: The person in a ranch-style home is somewhere to the right of the person who has red hair.
    ranch_idx = styles.index('ranch')
    red_idx = hair_colors.index('red')
    # Find house with red hair and house with ranch style
    red_houses = [If(hair_vars[h] == red_idx, h+1, -1) for h in range(4)]
    ranch_houses = [If(style_vars[h] == ranch_idx, h+1, -1) for h in range(4)]
    solver.add(Or([And(red_houses[r] != -1, ranch_houses[s] != -1, ranch_houses[s] > red_houses[r]) 
                  for r in range(4) for s in range(4)]))
    
    # Clue 6: Peter is the person's child is named Bella.
    peter_idx = names.index('Peter')
    bella_idx = children.index('Bella')
    solver.add(Exists([h], And(h >= 0, h < 4, name_vars[h] == peter_idx, child_vars[h] == bella_idx)))
    
    # Clue 7: Arnold is the person who has red hair.
    arnold_idx = names.index('Arnold')
    solver.add(Exists([h], And(h >= 0, h < 4, name_vars[h] == arnold_idx, hair_vars[h] == red_idx)))
    
    # Clue 8: Alice is the person living in a colonial-style house.
    colonial_idx = styles.index('colonial')
    solver.add(Exists([h], And(h >= 0, h < 4, name_vars[h] == alice_idx, style_vars[h] == colonial_idx)))
    
    # Clue 9: The person who has black hair is in the second house.
    black_idx = hair_colors.index('black')
    solver.add(hair_vars[1] == black_idx)
    
    # Clue 10: The person who loves fantasy books is Peter.
    fantasy_idx = book_genres.index('fantasy')
    solver.add(Exists([h], And(h >= 0, h < 4, name_vars[h] == peter_idx, book_vars[h] == fantasy_idx)))
    
    # Clue 11: Arnold is the person's child is named Meredith.
    meredith_idx = children.index('Meredith')
    solver.add(Exists([h], And(h >= 0, h < 4, name_vars[h] == arnold_idx, child_vars[h] == meredith_idx)))
    
    # Clue 12: The person who has black hair is Eric.
    eric_idx = names.index('Eric')
    solver.add(Exists([h], And(h >= 0, h < 4, name_vars[h] == eric_idx, hair_vars[h] == black_idx)))
    
    # Clue 13: The person who loves science fiction books is Arnold.
    scifi_idx = book_genres.index('science fiction')
    solver.add(Exists([h], And(h >= 0, h < 4, name_vars[h] == arnold_idx, book_vars[h] == scifi_idx)))
    
    # Check if solution exists
    if solver.check() == sat:
        model = solver.model()
        
        # Extract solution
        solution = []
        for house in houses:
            name_idx = model.evaluate(name_vars[house-1]).as_long()
            style_idx = model.evaluate(style_vars[house-1]).as_long()
            hair_idx = model.evaluate(hair_vars[house-1]).as_long()
            child_idx = model.evaluate(child_vars[house-1]).as_long()
            book_idx = model.evaluate(book_vars[house-1]).as_long()
            
            row = [
                str(house),
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