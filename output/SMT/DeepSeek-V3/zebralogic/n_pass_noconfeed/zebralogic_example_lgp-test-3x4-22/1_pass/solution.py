import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2, 3]
    
    # Define attributes
    names = ['Arnold', 'Eric', 'Peter']
    music_genres = ['pop', 'rock', 'classical']
    children = ['Fred', 'Meredith', 'Bella']
    book_genres = ['mystery', 'romance', 'science fiction']
    
    # Create variables for each attribute per house
    name_vars = [z3.Int(f'name_{h}') for h in houses]
    music_vars = [z3.Int(f'music_{h}') for h in houses]
    child_vars = [z3.Int(f'child_{h}') for h in houses]
    book_vars = [z3.Int(f'book_{h}') for h in houses]
    
    # Define domains for each variable type
    for h in houses:
        solver.add(z3.And(name_vars[h-1] >= 0, name_vars[h-1] < len(names)))
        solver.add(z3.And(music_vars[h-1] >= 0, music_vars[h-1] < len(music_genres)))
        solver.add(z3.And(child_vars[h-1] >= 0, child_vars[h-1] < len(children)))
        solver.add(z3.And(book_vars[h-1] >= 0, book_vars[h-1] < len(book_genres)))
    
    # All attributes must be unique within their category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(music_vars))
    solver.add(z3.Distinct(child_vars))
    solver.add(z3.Distinct(book_vars))
    
    # Clue 1: The person's child is named Fred is directly left of the person who loves mystery books.
    fred_index = children.index('Fred')
    mystery_index = book_genres.index('mystery')
    
    for h in [1, 2]:  # Only houses 1 and 2 can be directly left of another house
        solver.add(z3.Implies(
            child_vars[h-1] == fred_index,
            z3.And(book_vars[h] == mystery_index)
        ))
    
    # Clue 2: Peter is in the first house.
    peter_index = names.index('Peter')
    solver.add(name_vars[0] == peter_index)
    
    # Clue 3: The person who loves mystery books is the person who loves classical music.
    classical_index = music_genres.index('classical')
    for h in houses:
        solver.add(z3.Implies(
            book_vars[h-1] == mystery_index,
            music_vars[h-1] == classical_index
        ))
    
    # Clue 4: The person who loves science fiction books is the person's child is named Meredith.
    scifi_index = book_genres.index('science fiction')
    meredith_index = children.index('Meredith')
    for h in houses:
        solver.add(z3.Implies(
            book_vars[h-1] == scifi_index,
            child_vars[h-1] == meredith_index
        ))
    
    # Clue 5: Eric is the person who loves mystery books.
    eric_index = names.index('Eric')
    for h in houses:
        solver.add(z3.Implies(
            book_vars[h-1] == mystery_index,
            name_vars[h-1] == eric_index
        ))
    
    # Clue 6: The person who loves rock music is somewhere to the right of the person who loves romance books.
    rock_index = music_genres.index('rock')
    romance_index = book_genres.index('romance')
    
    # Find house with romance books
    romance_house = z3.Int('romance_house')
    solver.add(romance_house >= 1, romance_house <= 3)
    for h in houses:
        solver.add(z3.Implies(book_vars[h-1] == romance_index, romance_house == h))
    
    # Find house with rock music
    rock_house = z3.Int('rock_house')
    solver.add(rock_house >= 1, rock_house <= 3)
    for h in houses:
        solver.add(z3.Implies(music_vars[h-1] == rock_index, rock_house == h))
    
    solver.add(rock_house > romance_house)
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare solution data
        solution_data = {
            "solution": {
                "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
                "rows": []
            }
        }
        
        for h in houses:
            name_idx = model.evaluate(name_vars[h-1]).as_long()
            music_idx = model.evaluate(music_vars[h-1]).as_long()
            child_idx = model.evaluate(child_vars[h-1]).as_long()
            book_idx = model.evaluate(book_vars[h-1]).as_long()
            
            row = [
                str(h),
                names[name_idx],
                music_genres[music_idx],
                children[child_idx],
                book_genres[book_idx]
            ]
            solution_data["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(solution_data, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()