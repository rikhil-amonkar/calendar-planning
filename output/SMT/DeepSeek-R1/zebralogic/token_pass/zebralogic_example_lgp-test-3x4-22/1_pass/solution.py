import json
from z3 import *

def main():
    # Create the solver
    s = Solver()
    
    # Define the attributes
    names = ['Arnold', 'Eric', 'Peter']
    music_genres = ['pop', 'rock', 'classical']
    children = ['Fred', 'Meredith', 'Bella']
    book_genres = ['mystery', 'romance', 'science fiction']
    
    # Create integer variables for each attribute's house position
    name_vars = {name: Int(f'{name}_house') for name in names}
    music_vars = {genre: Int(f'{genre}_house') for genre in music_genres}
    child_vars = {child: Int(f'{child}_house') for child in children}
    book_vars = {genre: Int(f'{genre}_house') for genre in book_genres}
    
    # All attributes must be in houses 1-3
    for var in list(name_vars.values()) + list(music_vars.values()) + list(child_vars.values()) + list(book_vars.values()):
        s.add(And(var >= 1, var <= 3))
    
    # All attributes within each category are distinct
    s.add(Distinct([name_vars[n] for n in names]))
    s.add(Distinct([music_vars[m] for m in music_genres]))
    s.add(Distinct([child_vars[c] for c in children]))
    s.add(Distinct([book_vars[b] for b in book_genres]))
    
    # Clue 1: The person's child is named Fred is directly left of the person who loves mystery books.
    s.add(child_vars['Fred'] == book_vars['mystery'] - 1)
    
    # Clue 2: Peter is in the first house.
    s.add(name_vars['Peter'] == 1)
    
    # Clue 3: The person who loves mystery books is the person who loves classical music.
    s.add(book_vars['mystery'] == music_vars['classical'])
    
    # Clue 4: The person who loves science fiction books is the person's child is named Meredith.
    s.add(book_vars['science fiction'] == child_vars['Meredith'])
    
    # Clue 5: Eric is the person who loves mystery books.
    s.add(name_vars['Eric'] == book_vars['mystery'])
    
    # Clue 6: The person who loves rock music is somewhere to the right of the person who loves romance books.
    s.add(music_vars['rock'] > book_vars['romance'])
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        
        # Create inverse mappings from house number to attribute
        house_to_name = {}
        house_to_music = {}
        house_to_child = {}
        house_to_book = {}
        
        for name, var in name_vars.items():
            house = model[var].as_long()
            house_to_name[house] = name
            
        for genre, var in music_vars.items():
            house = model[var].as_long()
            house_to_music[house] = genre
            
        for child, var in child_vars.items():
            house = model[var].as_long()
            house_to_child[house] = child
            
        for genre, var in book_vars.items():
            house = model[var].as_long()
            house_to_book[house] = genre
        
        # Build the solution rows
        rows = []
        for house in range(1, 4):
            rows.append([
                str(house),
                house_to_name[house],
                house_to_music[house],
                house_to_child[house],
                house_to_book[house]
            ])
        
        # Create the solution dictionary
        solution = {
            "solution": {
                "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
                "rows": rows
            }
        }
        
        # Output as JSON
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()