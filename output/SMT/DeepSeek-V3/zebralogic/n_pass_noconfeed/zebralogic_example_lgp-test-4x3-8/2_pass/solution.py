import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2, 3, 4]
    
    # Define attributes
    names = ['Eric', 'Arnold', 'Peter', 'Alice']
    hair_colors = ['blonde', 'black', 'brown', 'red']
    music_genres = ['pop', 'jazz', 'rock', 'classical']
    
    # Create variables for each attribute per house
    name_vars = [z3.Int(f'name_{i}') for i in houses]
    hair_vars = [z3.Int(f'hair_{i}') for i in houses]
    music_vars = [z3.Int(f'music_{i}') for i in houses]
    
    # Constraint: all attributes are within valid ranges
    for i in houses:
        solver.add(z3.And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(z3.And(hair_vars[i-1] >= 0, hair_vars[i-1] < len(hair_colors)))
        solver.add(z3.And(music_vars[i-1] >= 0, music_vars[i-1] < len(music_genres)))
    
    # Constraint: all attributes are unique within their category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(hair_vars))
    solver.add(z3.Distinct(music_vars))
    
    # Clue 1: Eric is the person who has red hair.
    eric_index = names.index('Eric')
    red_index = hair_colors.index('red')
    for i in houses:
        solver.add(z3.Implies(name_vars[i-1] == eric_index, hair_vars[i-1] == red_index))
    
    # Clue 2: The person who loves classical music is directly left of the person who has blonde hair.
    classical_index = music_genres.index('classical')
    blonde_index = hair_colors.index('blonde')
    for i in range(1, 4):  # Houses 1-3 (since house 4 has no right neighbor)
        solver.add(z3.Implies(music_vars[i-1] == classical_index, hair_vars[i] == blonde_index))
    
    # Clue 3: The person who has brown hair is not in the first house.
    brown_index = hair_colors.index('brown')
    solver.add(hair_vars[0] != brown_index)
    
    # Clue 4: The person who loves pop music is not in the third house.
    pop_index = music_genres.index('pop')
    solver.add(music_vars[2] != pop_index)
    
    # Clue 5: The person who loves classical music is in the first house.
    solver.add(music_vars[0] == classical_index)
    
    # Clue 6: The person who loves jazz music is the person who has red hair.
    jazz_index = music_genres.index('jazz')
    for i in houses:
        solver.add(z3.Implies(music_vars[i-1] == jazz_index, hair_vars[i-1] == red_index))
    
    # Clue 7: The person who loves rock music is Arnold.
    rock_index = music_genres.index('rock')
    arnold_index = names.index('Arnold')
    for i in houses:
        solver.add(z3.Implies(music_vars[i-1] == rock_index, name_vars[i-1] == arnold_index))
    
    # Clue 8: Peter is somewhere to the right of the person who loves rock music.
    peter_index = names.index('Peter')
    # Create a constraint that Peter's house number is greater than Arnold's house number
    rock_house = z3.Int('rock_house')
    peter_house = z3.Int('peter_house')
    
    # Find which house has rock music (Arnold)
    for i in houses:
        solver.add(z3.Implies(music_vars[i-1] == rock_index, rock_house == i))
    
    # Find which house has Peter
    for i in houses:
        solver.add(z3.Implies(name_vars[i-1] == peter_index, peter_house == i))
    
    # Peter is to the right of rock lover (Arnold)
    solver.add(peter_house > rock_house)
    
    # Check satisfiability
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare solution data
        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor", "MusicGenre"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for i in houses:
            name_val = model.eval(name_vars[i-1]).as_long()
            hair_val = model.eval(hair_vars[i-1]).as_long()
            music_val = model.eval(music_vars[i-1]).as_long()
            
            row = [
                str(i),
                names[name_val],
                hair_colors[hair_val],
                music_genres[music_val]
            ]
            solution["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()