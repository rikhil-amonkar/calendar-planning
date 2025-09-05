import z3
import json

def main():
    # Define the attributes
    names = ['Eric', 'Arnold', 'Peter', 'Alice']
    hair_colors = ['blonde', 'black', 'brown', 'red']
    music_genres = ['pop', 'jazz', 'rock', 'classical']
    
    # Create Z3 enums for each attribute type and get their constants
    Name, name_consts = z3.EnumSort('Name', names)
    HairColor, hair_consts = z3.EnumSort('HairColor', hair_colors)
    MusicGenre, music_consts = z3.EnumSort('MusicGenre', music_genres)
    
    # Unpack the constants
    Eric, Arnold, Peter, Alice = name_consts
    blonde, black, brown, red = hair_consts
    pop, jazz, rock, classical = music_consts
    
    # Create variables for each house's attributes
    n = [z3.Const(f'n_{i}', Name) for i in range(4)]
    h = [z3.Const(f'h_{i}', HairColor) for i in range(4)]
    m = [z3.Const(f'm_{i}', MusicGenre) for i in range(4)]
    
    solver = z3.Solver()
    
    # All attributes are distinct
    solver.add(z3.Distinct(n))
    solver.add(z3.Distinct(h))
    solver.add(z3.Distinct(m))
    
    # Add clues
    # 1. Eric is the person who has red hair.
    for i in range(4):
        solver.add(z3.Implies(n[i] == Eric, h[i] == red))
    
    # 2. The person who loves classical music is directly left of the person who has blonde hair.
    for i in range(3):
        solver.add(z3.Implies(m[i] == classical, h[i+1] == blonde))
    
    # 3. The person who has brown hair is not in the first house.
    solver.add(h[0] != brown)
    
    # 4. The person who loves pop music is not in the third house.
    solver.add(m[2] != pop)
    
    # 5. The person who loves classical music is in the first house.
    solver.add(m[0] == classical)
    
    # 6. The person who loves jazz music is the person who has red hair.
    for i in range(4):
        solver.add(z3.Implies(m[i] == jazz, h[i] == red))
    
    # 7. The person who loves rock music is Arnold.
    for i in range(4):
        solver.add(z3.Implies(m[i] == rock, n[i] == Arnold))
    
    # 8. Peter is somewhere to the right of the person who loves rock music.
    # Find rock music house index and Peter's index must be greater
    rock_index = z3.Int('rock_index')
    peter_index = z3.Int('peter_index')
    solver.add(rock_index >= 0, rock_index < 4)
    solver.add(peter_index >= 0, peter_index < 4)
    for i in range(4):
        solver.add(z3.Implies(m[i] == rock, rock_index == i))
        solver.add(z3.Implies(n[i] == Peter, peter_index == i))
    solver.add(peter_index > rock_index)
    
    # Check satisfiability
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Extract values for each house
        rows = []
        for i in range(4):
            house_num = str(i+1)
            name_val = model.eval(n[i])
            hair_val = model.eval(h[i])
            music_val = model.eval(m[i])
            
            # Convert Z3 symbols to strings by comparing with constants
            name_str = next(name for name, const in zip(names, name_consts) if z3.eq(name_val, const))
            hair_str = next(color for color, const in zip(hair_colors, hair_consts) if z3.eq(hair_val, const))
            music_str = next(genre for genre, const in zip(music_genres, music_consts) if z3.eq(music_val, const))
            
            rows.append([house_num, name_str, hair_str, music_str])
        
        # Create JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor", "MusicGenre"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()