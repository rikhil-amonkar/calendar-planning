import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2, 3]
    
    # Define attributes
    names = ['Eric', 'Arnold', 'Peter']
    smoothies = ['desert', 'watermelon', 'cherry']
    book_genres = ['science fiction', 'romance', 'mystery']
    
    # Create variables for each attribute per house
    name_vars = [z3.Int(f'name_{h}') for h in houses]
    smoothie_vars = [z3.Int(f'smoothie_{h}') for h in houses]
    book_vars = [z3.Int(f'book_{h}') for h in houses]
    
    # Constraint: All attributes are distinct within their category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(smoothie_vars))
    solver.add(z3.Distinct(book_vars))
    
    # Constraint: All variables must be within valid range (0-2 for indices)
    for h in houses:
        solver.add(name_vars[h-1] >= 0, name_vars[h-1] < len(names))
        solver.add(smoothie_vars[h-1] >= 0, smoothie_vars[h-1] < len(smoothies))
        solver.add(book_vars[h-1] >= 0, book_vars[h-1] < len(book_genres))
    
    # Clue 1: The person who likes Cherry smoothies is somewhere to the left of the person who loves mystery books
    cherry_index = smoothies.index('cherry')
    mystery_index = book_genres.index('mystery')
    
    # Create Z3 variables for cherry and mystery houses
    cherry_house = z3.Int('cherry_house')
    mystery_house = z3.Int('mystery_house')
    
    # Constraint: cherry_house and mystery_house must be valid house numbers
    solver.add(cherry_house >= 1, cherry_house <= 3)
    solver.add(mystery_house >= 1, mystery_house <= 3)
    
    # Link smoothie/book variables to house variables
    for h in houses:
        solver.add(z3.Implies(smoothie_vars[h-1] == cherry_index, cherry_house == h))
        solver.add(z3.Implies(book_vars[h-1] == mystery_index, mystery_house == h))
    
    solver.add(cherry_house < mystery_house)
    
    # Clue 2: Arnold is the person who loves mystery books
    arnold_index = names.index('Arnold')
    solver.add(z3.Or([z3.And(book_vars[h-1] == mystery_index, name_vars[h-1] == arnold_index) for h in houses]))
    
    # Clue 3: The person who loves science fiction books is not in the first house
    scifi_index = book_genres.index('science fiction')
    solver.add(book_vars[0] != scifi_index)
    
    # Clue 4: The Desert smoothie lover is directly left of the person who loves mystery books
    desert_index = smoothies.index('desert')
    # Create constraint that mystery_house is not 1 (since someone must be directly left)
    solver.add(mystery_house > 1)
    # Add constraint that the house directly left of mystery_house has desert smoothie
    for h in houses:
        if h > 1:  # Only houses 2 and 3 can have someone directly left
            solver.add(z3.Implies(mystery_house == h, smoothie_vars[h-2] == desert_index))
    
    # Clue 5: Peter is in the first house
    peter_index = names.index('Peter')
    solver.add(name_vars[0] == peter_index)
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare solution data
        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "BookGenre"],
                "rows": []
            }
        }
        
        for h in houses:
            name_val = model.eval(name_vars[h-1]).as_long()
            smoothie_val = model.eval(smoothie_vars[h-1]).as_long()
            book_val = model.eval(book_vars[h-1]).as_long()
            
            row = [
                str(h),
                names[name_val],
                smoothies[smoothie_val],
                book_genres[book_val]
            ]
            solution["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()