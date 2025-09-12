import z3
import json

def main():
    solver = z3.Solver()
    
    houses = [1, 2, 3, 4, 5, 6]
    
    names = ['Arnold', 'Eric', 'Peter', 'Alice', 'Carol', 'Bob']
    genres = ['jazz', 'pop', 'classical', 'rock', 'hip hop', 'country']
    
    name_vars = {name: z3.Int(f'name_{name}') for name in names}
    genre_vars = {genre: z3.Int(f'genre_{genre}') for genre in genres}
    
    for name in names:
        solver.add(z3.And(name_vars[name] >= 1, name_vars[name] <= 6))
    for genre in genres:
        solver.add(z3.And(genre_vars[genre] >= 1, genre_vars[genre] <= 6))
    
    solver.add(z3.Distinct([name_vars[name] for name in names]))
    solver.add(z3.Distinct([genre_vars[genre] for genre in genres]))
    
    # Clue 1: Bob is directly left of the person who loves jazz music.
    solver.add(name_vars['Bob'] == genre_vars['jazz'] - 1)
    
    # Clue 2: Eric is somewhere to the left of the person who loves hip-hop music.
    solver.add(name_vars['Eric'] < genre_vars['hip hop'])
    
    # Clue 3: Carol is in the sixth house.
    solver.add(name_vars['Carol'] == 6)
    
    # Clue 4: Eric and the person who loves hip-hop music are next to each other.
    solver.add(z3.Or(
        name_vars['Eric'] == genre_vars['hip hop'] - 1,
        name_vars['Eric'] == genre_vars['hip hop'] + 1
    ))
    
    # Clue 5: The person who loves country music is Carol.
    solver.add(genre_vars['country'] == name_vars['Carol'])
    
    # Clue 6: Arnold is not in the fifth house.
    solver.add(name_vars['Arnold'] != 5)
    
    # Clue 7: Arnold is somewhere to the right of the person who loves pop music.
    solver.add(name_vars['Arnold'] > genre_vars['pop'])
    
    # Clue 8: The person who loves pop music is Peter.
    solver.add(genre_vars['pop'] == name_vars['Peter'])
    
    # Clue 9: The person who loves hip-hop music is in the third house.
    solver.add(genre_vars['hip hop'] == 3)
    
    # Clue 10: There is one house between Peter and Bob.
    solver.add(z3.Or(
        name_vars['Peter'] == name_vars['Bob'] + 2,
        name_vars['Peter'] == name_vars['Bob'] - 2
    ))
    
    # Clue 11: The person who loves rock music is not in the fifth house.
    solver.add(genre_vars['rock'] != 5)
    
    if solver.check() == z3.sat:
        model = solver.model()
        
        result = []
        for house in houses:
            row = [str(house)]
            
            for name in names:
                if model.evaluate(name_vars[name]).as_long() == house:
                    row.append(name)
                    break
            
            for genre in genres:
                if model.evaluate(genre_vars[genre]).as_long() == house:
                    row.append(genre)
                    break
            
            result.append(row)
        
        output = {
            "solution": {
                "header": ["House", "Name", "MusicGenre"],
                "rows": result
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()