from z3 import *
import json

def main():
    # Create solver
    solver = Solver()
    
    # Define the houses
    n = 6
    houses = [1, 2, 3, 4, 5, 6]
    
    # Define attributes
    names = ['Eric', 'Alice', 'Arnold', 'Carol', 'Peter', 'Bob']
    styles = ['mediterranean', 'modern', 'craftsman', 'ranch', 'colonial', 'victorian']
    genres = ['country', 'hip hop', 'pop', 'jazz', 'classical', 'rock']
    hobbies = ['cooking', 'painting', 'photography', 'woodworking', 'gardening', 'knitting']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in houses]
    style_vars = [Int(f'style_{i}') for i in houses]
    genre_vars = [Int(f'genre_{i}') for i in houses]
    hobby_vars = [Int(f'hobby_{i}') for i in houses]
    
    # Domain constraints - each variable gets a value from 0 to 5
    for i in houses:
        solver.add(And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(And(style_vars[i-1] >= 0, style_vars[i-1] < len(styles)))
        solver.add(And(genre_vars[i-1] >= 0, genre_vars[i-1] < len(genres)))
        solver.add(And(hobby_vars[i-1] >= 0, hobby_vars[i-1] < len(hobbies)))
    
    # All attributes are distinct per house
    solver.add(Distinct(name_vars))
    solver.add(Distinct(style_vars))
    solver.add(Distinct(genre_vars))
    solver.add(Distinct(hobby_vars))
    
    # Clue 1: The person who loves rock music is in the fifth house.
    rock_idx = genres.index('rock')
    solver.add(genre_vars[4] == rock_idx)
    
    # Clue 2: The person who loves classical music and the woodworking hobbyist are next to each other.
    classical_idx = genres.index('classical')
    woodworking_idx = hobbies.index('woodworking')
    for i in range(n-1):
        solver.add(Or(
            And(genre_vars[i] == classical_idx, hobby_vars[i+1] == woodworking_idx),
            And(genre_vars[i+1] == classical_idx, hobby_vars[i] == woodworking_idx)
        ))
    
    # Clue 3: The person in a Mediterranean-style villa is the person who loves hip-hop music.
    mediterranean_idx = styles.index('mediterranean')
    hiphop_idx = genres.index('hip hop')
    for i in houses:
        solver.add(Implies(style_vars[i-1] == mediterranean_idx, genre_vars[i-1] == hiphop_idx))
    
    # Clue 4: There are two houses between Arnold and the person residing in a Victorian house.
    arnold_idx = names.index('Arnold')
    victorian_idx = styles.index('victorian')
    for i in range(n):
        for j in range(n):
            if abs(i - j) == 3:  # Two houses between means distance of 3 positions
                solver.add(Or(
                    And(name_vars[i] == arnold_idx, style_vars[j] == victorian_idx),
                    And(name_vars[j] == arnold_idx, style_vars[i] == victorian_idx)
                ))
    
    # Clue 5: The person who loves jazz music is directly left of Eric.
    jazz_idx = genres.index('jazz')
    eric_idx = names.index('Eric')
    for i in range(n-1):
        solver.add(Implies(genre_vars[i] == jazz_idx, name_vars[i+1] == eric_idx))
    
    # Clue 6: The person who loves hip-hop music is somewhere to the left of the person who enjoys knitting.
    knitting_idx = hobbies.index('knitting')
    for i in range(n):
        for j in range(i+1, n):
            solver.add(Implies(genre_vars[i] == hiphop_idx, hobby_vars[j] == knitting_idx))
    
    # Clue 7: Carol is the person who loves hip-hop music.
    carol_idx = names.index('Carol')
    for i in houses:
        solver.add(Implies(name_vars[i-1] == carol_idx, genre_vars[i-1] == hiphop_idx))
    
    # Clue 8: The person in a Craftsman-style house is Arnold.
    craftsman_idx = styles.index('craftsman')
    for i in houses:
        solver.add(Implies(style_vars[i-1] == craftsman_idx, name_vars[i-1] == arnold_idx))
    
    # Clue 9: The person in a ranch-style home is Eric.
    ranch_idx = styles.index('ranch')
    for i in houses:
        solver.add(Implies(style_vars[i-1] == ranch_idx, name_vars[i-1] == eric_idx))
    
    # Clue 10: The woodworking hobbyist is the person residing in a Victorian house.
    for i in houses:
        solver.add(Implies(hobby_vars[i-1] == woodworking_idx, style_vars[i-1] == victorian_idx))
    
    # Clue 11: The person who loves country music is in the first house.
    country_idx = genres.index('country')
    solver.add(genre_vars[0] == country_idx)
    
    # Clue 12: There is one house between the person who paints as a hobby and the person living in a colonial-style house.
    painting_idx = hobbies.index('painting')
    colonial_idx = styles.index('colonial')
    for i in range(n):
        for j in range(n):
            if abs(i - j) == 2:  # One house between means distance of 2 positions
                solver.add(Or(
                    And(hobby_vars[i] == painting_idx, style_vars[j] == colonial_idx),
                    And(hobby_vars[j] == painting_idx, style_vars[i] == colonial_idx)
                ))
    
    # Clue 13: Alice is the photography enthusiast.
    alice_idx = names.index('Alice')
    photography_idx = hobbies.index('photography')
    for i in houses:
        solver.add(Implies(name_vars[i-1] == alice_idx, hobby_vars[i-1] == photography_idx))
    
    # Clue 14: The person who enjoys gardening is Eric.
    gardening_idx = hobbies.index('gardening')
    for i in houses:
        solver.add(Implies(hobby_vars[i-1] == gardening_idx, name_vars[i-1] == eric_idx))
    
    # Clue 15: Bob is in the third house.
    bob_idx = names.index('Bob')
    solver.add(name_vars[2] == bob_idx)
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        
        # Extract the solution
        solution = []
        for i in range(n):
            house_num = i + 1
            name_idx = model.eval(name_vars[i]).as_long()
            style_idx = model.eval(style_vars[i]).as_long()
            genre_idx = model.eval(genre_vars[i]).as_long()
            hobby_idx = model.eval(hobby_vars[i]).as_long()
            
            row = [
                str(house_num),
                names[name_idx],
                styles[style_idx],
                genres[genre_idx],
                hobbies[hobby_idx]
            ]
            solution.append(row)
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
                "rows": solution
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()