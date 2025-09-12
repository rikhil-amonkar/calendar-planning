import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define attributes
    names = ['Arnold', 'Peter', 'Eric', 'Alice']
    styles = ['craftsman', 'colonial', 'victorian', 'ranch']
    hairs = ['red', 'blonde', 'black', 'brown']
    children = ['Bella', 'Fred', 'Meredith', 'Samantha']
    books = ['mystery', 'fantasy', 'romance', 'science fiction']
    
    # Create variables for each house and attribute
    name_vars = [z3.Int(f'name_{i}') for i in range(1,5)]
    style_vars = [z3.Int(f'style_{i}') for i in range(1,5)]
    hair_vars = [z3.Int(f'hair_{i}') for i in range(1,5)]
    child_vars = [z3.Int(f'child_{i}') for i in range(1,5)]
    book_vars = [z3.Int(f'book_{i}') for i in range(1,5)]
    
    # Constrain all variables to be between 0 and 3 (representing indices)
    for i in range(4):
        solver.add(z3.And(name_vars[i] >= 0, name_vars[i] < 4))
        solver.add(z3.And(style_vars[i] >= 0, style_vars[i] < 4))
        solver.add(z3.And(hair_vars[i] >= 0, hair_vars[i] < 4))
        solver.add(z3.And(child_vars[i] >= 0, child_vars[i] < 4))
        solver.add(z3.And(book_vars[i] >= 0, book_vars[i] < 4))
    
    # All attributes must be distinct per category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(style_vars))
    solver.add(z3.Distinct(hair_vars))
    solver.add(z3.Distinct(child_vars))
    solver.add(z3.Distinct(book_vars))
    
    # Add clues
    # 1. Craftsman-style house is in the third house
    solver.add(style_vars[2] == styles.index('craftsman'))
    
    # 2. Alice loves romance books
    solver.add(z3.Exists([i], z3.And(i >= 0, i < 4, name_vars[i] == names.index('Alice'), book_vars[i] == books.index('romance'))))
    
    # 3. Brown hair in fourth house
    solver.add(hair_vars[3] == hairs.index('brown'))
    
    # 4. Child Samantha in fourth house
    solver.add(child_vars[3] == children.index('Samantha'))
    
    # 5. Ranch-style home is right of red hair
    # Find red hair position and ranch position, then ranch position > red hair position
    red_hair_pos = z3.Int('red_hair_pos')
    ranch_style_pos = z3.Int('ranch_style_pos')
    solver.add(z3.And(red_hair_pos >= 0, red_hair_pos < 4))
    solver.add(z3.And(ranch_style_pos >= 0, ranch_style_pos < 4))
    solver.add(z3.ForAll([i], z3.Implies(hair_vars[i] == hairs.index('red'), red_hair_pos == i)))
    solver.add(z3.ForAll([i], z3.Implies(style_vars[i] == styles.index('ranch'), ranch_style_pos == i)))
    solver.add(ranch_style_pos > red_hair_pos)
    
    # 6. Peter has child Bella
    solver.add(z3.Exists([i], z3.And(i >= 0, i < 4, name_vars[i] == names.index('Peter'), child_vars[i] == children.index('Bella'))))
    
    # 7. Arnold has red hair
    solver.add(z3.Exists([i], z3.And(i >= 0, i < 4, name_vars[i] == names.index('Arnold'), hair_vars[i] == hairs.index('red'))))
    
    # 8. Alice lives in colonial-style house
    solver.add(z3.Exists([i], z3.And(i >= 0, i < 4, name_vars[i] == names.index('Alice'), style_vars[i] == styles.index('colonial'))))
    
    # 9. Black hair in second house
    solver.add(hair_vars[1] == hairs.index('black'))
    
    # 10. Peter loves fantasy books
    solver.add(z3.Exists([i], z3.And(i >= 0, i < 4, name_vars[i] == names.index('Peter'), book_vars[i] == books.index('fantasy'))))
    
    # 11. Arnold has child Meredith
    solver.add(z3.Exists([i], z3.And(i >= 0, i < 4, name_vars[i] == names.index('Arnold'), child_vars[i] == children.index('Meredith'))))
    
    # 12. Black hair is Eric
    solver.add(z3.Exists([i], z3.And(i >= 0, i < 4, hair_vars[i] == hairs.index('black'), name_vars[i] == names.index('Eric'))))
    
    # 13. Arnold loves science fiction books
    solver.add(z3.Exists([i], z3.And(i >= 0, i < 4, name_vars[i] == names.index('Arnold'), book_vars[i] == books.index('science fiction'))))
    
    # Check and get model
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare results
        rows = []
        for i in range(4):
            name_idx = model.evaluate(name_vars[i]).as_long()
            style_idx = model.evaluate(style_vars[i]).as_long()
            hair_idx = model.evaluate(hair_vars[i]).as_long()
            child_idx = model.evaluate(child_vars[i]).as_long()
            book_idx = model.evaluate(book_vars[i]).as_long()
            
            row = [
                str(i+1),
                names[name_idx],
                styles[style_idx],
                hairs[hair_idx],
                children[child_idx],
                books[book_idx]
            ]
            rows.append(row)
        
        # Create JSON output
        output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
                "rows": rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()