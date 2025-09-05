import json
from z3 import *

def main():
    # Initialize the solver
    solver = Solver()
    
    # House indices
    houses = [1, 2, 3, 4, 5, 6]
    
    # Define the attributes with indices
    names = ['Arnold', 'Eric', 'Peter', 'Alice', 'Carol', 'Bob']
    music_genres = ['jazz', 'pop', 'classical', 'rock', 'hip hop', 'country']
    
    # Create integer variables for each house's name and music genre
    name_vars = [Int(f'name_{i}') for i in houses]
    music_vars = [Int(f'music_{i}') for i in houses]
    
    # Create position variables for each name and music genre
    name_pos_vars = [Int(f'{name}_pos') for name in names]
    music_pos_vars = [Int(f'{genre}_pos') for genre in music_genres]
    
    # Constraints: each name and music variable must be within valid range
    for i in houses:
        solver.add(name_vars[i-1] >= 0, name_vars[i-1] < len(names))
        solver.add(music_vars[i-1] >= 0, music_vars[i-1] < len(music_genres))
    
    # Constraints: all names and music genres are distinct per house
    solver.add(Distinct(name_vars))
    solver.add(Distinct(music_vars))
    
    # Constraints: position variables are between 1 and 6
    for pos_var in name_pos_vars + music_pos_vars:
        solver.add(pos_var >= 1, pos_var <= 6)
    
    # Constraints: position variables are distinct for names and for music genres
    solver.add(Distinct(name_pos_vars))
    solver.add(Distinct(music_pos_vars))
    
    # Link the house variables to the position variables
    for idx, name in enumerate(names):
        for house in houses:
            solver.add(Implies(name_vars[house-1] == idx, name_pos_vars[idx] == house))
    
    for idx, genre in enumerate(music_genres):
        for house in houses:
            solver.add(Implies(music_vars[house-1] == idx, music_pos_vars[idx] == house))
    
    # Define specific position variables for easier reference
    Arnold_pos, Eric_pos, Peter_pos, Alice_pos, Carol_pos, Bob_pos = name_pos_vars
    jazz_pos, pop_pos, classical_pos, rock_pos, hip_hop_pos, country_pos = music_pos_vars
    
    # Add clues as constraints
    # 1. Bob is directly left of the person who loves jazz music.
    solver.add(Bob_pos == jazz_pos - 1)
    
    # 2. Eric is somewhere to the left of the person who loves hip-hop music.
    solver.add(Eric_pos < hip_hop_pos)
    
    # 3. Carol is in the sixth house.
    solver.add(Carol_pos == 6)
    
    # 4. Eric and the person who loves hip-hop music are next to each other.
    solver.add(Or(Eric_pos == hip_hop_pos - 1, Eric_pos == hip_hop_pos + 1))
    
    # 5. The person who loves country music is Carol.
    solver.add(country_pos == Carol_pos)
    
    # 6. Arnold is not in the fifth house.
    solver.add(Arnold_pos != 5)
    
    # 7. Arnold is somewhere to the right of the person who loves pop music.
    solver.add(Arnold_pos > pop_pos)
    
    # 8. The person who loves pop music is Peter.
    solver.add(pop_pos == Peter_pos)
    
    # 9. The person who loves hip-hop music is in the third house.
    solver.add(hip_hop_pos == 3)
    
    # 10. There is one house between Peter and Bob.
    solver.add(Or(Peter_pos == Bob_pos + 2, Peter_pos == Bob_pos - 2))
    
    # 11. The person who loves rock music is not in the fifth house.
    solver.add(rock_pos != 5)
    
    # Check if the solver is satisfied and get the model
    if solver.check() == sat:
        model = solver.model()
        
        # Retrieve the name and music for each house
        result = []
        for i in houses:
            name_index = model.evaluate(name_vars[i-1]).as_long()
            music_index = model.evaluate(music_vars[i-1]).as_long()
            result.append({
                'house': i,
                'name': names[name_index],
                'music': music_genres[music_index]
            })
        
        # Sort by house number to ensure order
        result.sort(key=lambda x: x['house'])
        
        # Format the output as required JSON
        output = {
            "solution": {
                "header": ["House", "Name", "MusicGenre"],
                "rows": [
                    [str(row['house']), row['name'], row['music']]
                    for row in result
                ]
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()