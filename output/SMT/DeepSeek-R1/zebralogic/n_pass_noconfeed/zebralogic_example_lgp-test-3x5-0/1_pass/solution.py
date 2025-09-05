import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define attributes and their possible values
    names = ['Peter', 'Arnold', 'Eric']
    books = ['science fiction', 'mystery', 'romance']
    smoothies = ['watermelon', 'desert', 'cherry']
    birthdays = ['april', 'jan', 'sept']
    heights = ['average', 'very short', 'short']
    
    # Create Z3 variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in range(1,4)]
    book_vars = [Int(f'book_{i}') for i in range(1,4)]
    smoothie_vars = [Int(f'smoothie_{i}') for i in range(1,4)]
    birthday_vars = [Int(f'birthday_{i}') for i in range(1,4)]
    height_vars = [Int(f'height_{i}') for i in range(1,4)]
    
    # Assert that all attributes are within their domains
    for var in name_vars:
        solver.add(var >= 0, var < 3)
    for var in book_vars:
        solver.add(var >= 0, var < 3)
    for var in smoothie_vars:
        solver.add(var >= 0, var < 3)
    for var in birthday_vars:
        solver.add(var >= 0, var < 3)
    for var in height_vars:
        solver.add(var >= 0, var < 3)
    
    # Assert all attributes are distinct
    solver.add(Distinct(name_vars))
    solver.add(Distinct(book_vars))
    solver.add(Distinct(smoothie_vars))
    solver.add(Distinct(birthday_vars))
    solver.add(Distinct(height_vars))
    
    # Add constraints from clues
    # 1. Cherry smoothie not in second house
    solver.add(smoothie_vars[1] != 2)  # cherry=2
    
    # 2. Arnold loves mystery books
    solver.add(Exists([i], And(i >= 0, i < 3, name_vars[i] == 1, book_vars[i] == 1)))  # Arnold=1, mystery=1
    
    # 3. January birthday not in first house
    solver.add(birthday_vars[0] != 1)  # jan=1
    
    # 4. Very short person loves romance books
    solver.add(Exists([i], And(i >= 0, i < 3, height_vars[i] == 1, book_vars[i] == 2)))  # very short=1, romance=2
    
    # 5. Mystery book lover has September birthday
    solver.add(Exists([i], And(i >= 0, i < 3, book_vars[i] == 1, birthday_vars[i] == 2)))  # mystery=1, sept=2
    
    # 6. Average height is Desert smoothie lover
    solver.add(Exists([i], And(i >= 0, i < 3, height_vars[i] == 0, smoothie_vars[i] == 1)))  # average=0, desert=1
    
    # 7. Eric in first house
    solver.add(name_vars[0] == 2)  # Eric=2
    
    # 8. Watermelon smoothie lover is short
    solver.add(Exists([i], And(i >= 0, i < 3, smoothie_vars[i] == 0, height_vars[i] == 2)))  # watermelon=0, short=2
    
    # 9. Watermelon smoothie lover is Eric
    solver.add(Exists([i], And(i >= 0, i < 3, smoothie_vars[i] == 0, name_vars[i] == 2)))  # watermelon=0, Eric=2
    
    # Check if solution exists
    if solver.check() == sat:
        model = solver.model()
        
        # Map integer values back to strings
        result = []
        for i in range(3):
            name_val = model.eval(name_vars[i]).as_long()
            book_val = model.eval(book_vars[i]).as_long()
            smoothie_val = model.eval(smoothie_vars[i]).as_long()
            birthday_val = model.eval(birthday_vars[i]).as_long()
            height_val = model.eval(height_vars[i]).as_long()
            
            result.append([
                str(i+1),
                names[name_val],
                books[book_val],
                smoothies[smoothie_val],
                birthdays[birthday_val],
                heights[height_val]
            ])
        
        # Create JSON output
        output = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()