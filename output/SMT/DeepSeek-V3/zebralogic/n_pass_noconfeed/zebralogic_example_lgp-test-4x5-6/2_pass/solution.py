from z3 import *
import json

def main():
    solver = Solver()
    
    # Define the attributes and their possible values
    names = ['Peter', 'Eric', 'Alice', 'Arnold']
    educations = ['bachelor', 'high school', 'associate', 'master']
    music_genres = ['jazz', 'rock', 'pop', 'classical']
    colors = ['green', 'red', 'yellow', 'white']
    flowers = ['lilies', 'carnations', 'daffodils', 'roses']
    
    # Create variables for each attribute in each house
    name_vars = [Int(f'name_{i}') for i in range(1, 5)]
    education_vars = [Int(f'education_{i}') for i in range(1, 5)]
    music_vars = [Int(f'music_{i}') for i in range(1, 5)]
    color_vars = [Int(f'color_{i}') for i in range(1, 5)]
    flower_vars = [Int(f'flower_{i}') for i in range(1, 5)]
    
    # Define the domain for each variable
    for i in range(4):
        solver.add(And(name_vars[i] >= 0, name_vars[i] < 4))
        solver.add(And(education_vars[i] >= 0, education_vars[i] < 4))
        solver.add(And(music_vars[i] >= 0, music_vars[i] < 4))
        solver.add(And(color_vars[i] >= 0, color_vars[i] < 4))
        solver.add(And(flower_vars[i] >= 0, flower_vars[i] < 4))
    
    # All attributes must be unique within their category
    solver.add(Distinct(name_vars))
    solver.add(Distinct(education_vars))
    solver.add(Distinct(music_vars))
    solver.add(Distinct(color_vars))
    solver.add(Distinct(flower_vars))
    
    # Clue 1: The person with a bachelor's degree is the person who loves a bouquet of daffodils.
    bachelor_idx = educations.index('bachelor')
    daffodils_idx = flowers.index('daffodils')
    for i in range(4):
        solver.add(Implies(education_vars[i] == bachelor_idx, flower_vars[i] == daffodils_idx))
    
    # Clue 2: The person who loves a carnations arrangement is not in the first house.
    carnations_idx = flowers.index('carnations')
    solver.add(flower_vars[0] != carnations_idx)
    
    # Clue 3: The person with a master's degree is Alice.
    master_idx = educations.index('master')
    alice_idx = names.index('Alice')
    for i in range(4):
        solver.add(Implies(education_vars[i] == master_idx, name_vars[i] == alice_idx))
    
    # Clue 4: The person with a master's degree is directly left of the person who loves classical music.
    classical_idx = music_genres.index('classical')
    # Create a constraint that master's degree is exactly one position left of classical music
    master_positions = []
    for i in range(3):  # Only positions 0,1,2 can have master's degree (since it must be left of classical)
        master_positions.append(And(education_vars[i] == master_idx, music_vars[i+1] == classical_idx))
    solver.add(Or(master_positions))
    
    # Clue 5: Eric is not in the second house.
    eric_idx = names.index('Eric')
    solver.add(name_vars[1] != eric_idx)
    
    # Clue 6: Arnold is not in the third house.
    arnold_idx = names.index('Arnold')
    solver.add(name_vars[2] != arnold_idx)
    
    # Clue 7: The person who loves yellow is directly left of the person who loves the rose bouquet.
    yellow_idx = colors.index('yellow')
    roses_idx = flowers.index('roses')
    for i in range(3):
        solver.add(Implies(color_vars[i] == yellow_idx, flower_vars[i+1] == roses_idx))
    
    # Clue 8: The person who loves pop music is in the second house.
    pop_idx = music_genres.index('pop')
    solver.add(music_vars[1] == pop_idx)
    
    # Clue 9: The person with an associate's degree is not in the fourth house.
    associate_idx = educations.index('associate')
    solver.add(education_vars[3] != associate_idx)
    
    # Clue 10: The person who loves a carnations arrangement is not in the fourth house.
    solver.add(flower_vars[3] != carnations_idx)
    
    # Clue 11: The person whose favorite color is red is directly left of the person who loves white.
    red_idx = colors.index('red')
    white_idx = colors.index('white')
    for i in range(3):
        solver.add(Implies(color_vars[i] == red_idx, color_vars[i+1] == white_idx))
    
    # Clue 12: The person whose favorite color is red is the person who loves rock music.
    rock_idx = music_genres.index('rock')
    for i in range(4):
        solver.add(Implies(color_vars[i] == red_idx, music_vars[i] == rock_idx))
    
    # Clue 13: Arnold is the person who loves yellow.
    for i in range(4):
        solver.add(Implies(name_vars[i] == arnold_idx, color_vars[i] == yellow_idx))
    
    # Clue 14: The person who loves a bouquet of daffodils is the person who loves yellow.
    for i in range(4):
        solver.add(Implies(flower_vars[i] == daffodils_idx, color_vars[i] == yellow_idx))
    
    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        
        # Create result structure
        header = ["House", "Name", "Education", "MusicGenre", "Color", "Flower"]
        rows = []
        
        for i in range(4):
            name_val = model.evaluate(name_vars[i]).as_long()
            education_val = model.evaluate(education_vars[i]).as_long()
            music_val = model.evaluate(music_vars[i]).as_long()
            color_val = model.evaluate(color_vars[i]).as_long()
            flower_val = model.evaluate(flower_vars[i]).as_long()
            
            row = [
                str(i + 1),
                names[name_val],
                educations[education_val],
                music_genres[music_val],
                colors[color_val],
                flowers[flower_val]
            ]
            rows.append(row)
        
        # Create the solution dictionary
        solution_dict = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        
        # Output as JSON
        print(json.dumps(solution_dict, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()