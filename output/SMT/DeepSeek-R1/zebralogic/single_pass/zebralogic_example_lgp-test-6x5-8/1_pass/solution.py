from z3 import *

def main():
    # Define attribute values
    names = ['Arnold', 'Peter', 'Bob', 'Eric', 'Carol', 'Alice']
    animals = ['horse', 'rabbit', 'fish', 'cat', 'bird', 'dog']
    occupations = ['engineer', 'nurse', 'lawyer', 'teacher', 'artist', 'doctor']
    sports = ['basketball', 'volleyball', 'soccer', 'tennis', 'baseball', 'swimming']
    heights = ['average', 'tall', 'short', 'very short', 'very tall', 'super tall']
    
    # Create attribute dictionaries for easy lookup
    attr_dict = {
        'Name': names,
        'Animal': animals,
        'Occupation': occupations,
        'FavoriteSport': sports,
        'Height': heights
    }
    
    # Create index mappings for each attribute
    name_to_idx = {n: i for i, n in enumerate(names)}
    animal_to_idx = {a: i for i, a in enumerate(animals)}
    occupation_to_idx = {o: i for i, o in enumerate(occupations)}
    sport_to_idx = {s: i for i, s in enumerate(sports)}
    height_to_idx = {h: i for i, h in enumerate(heights)}
    
    # Initialize Z3 variables for each attribute per house
    name_vars = [Int(f'name_{i+1}') for i in range(6)]
    animal_vars = [Int(f'animal_{i+1}') for i in range(6)]
    occupation_vars = [Int(f'occupation_{i+1}') for i in range(6)]
    sport_vars = [Int(f'sport_{i+1}') for i in range(6)]
    height_vars = [Int(f'height_{i+1}') for i in range(6)]
    
    solver = Solver()
    
    # Add constraints: each attribute variable must be between 0 and 5
    for var_list in [name_vars, animal_vars, occupation_vars, sport_vars, height_vars]:
        for var in var_list:
            solver.add(var >= 0, var < 6)
        solver.add(Distinct(var_list))
    
    # Clue 1: The engineer owns the dog
    engineer_idx = occupation_to_idx['engineer']
    dog_idx = animal_to_idx['dog']
    for i in range(6):
        solver.add(Implies(occupation_vars[i] == engineer_idx, animal_vars[i] == dog_idx))
    
    # Clue 2: Average height is left of short height
    avg_idx = height_to_idx['average']
    short_idx = height_to_idx['short']
    solver.add(Or([And(height_vars[i] == avg_idx, height_vars[j] == short_idx) for i in range(6) for j in range(6) if i < j]))
    
    # Clue 3: Average height is directly left of rabbit owner
    rabbit_idx = animal_to_idx['rabbit']
    solver.add(Or([And(height_vars[i] == avg_idx, animal_vars[i+1] == rabbit_idx) for i in range(5)]))
    
    # Clue 4: Tall height is left of very short height
    tall_idx = height_to_idx['tall']
    very_short_idx = height_to_idx['very short']
    solver.add(Or([And(height_vars[i] == tall_idx, height_vars[j] == very_short_idx) for i in range(6) for j in range(6) if i < j]))
    
    # Clue 5: Arnold is the cat owner
    arnold_idx = name_to_idx['Arnold']
    cat_idx = animal_to_idx['cat']
    for i in range(6):
        solver.add(Implies(name_vars[i] == arnold_idx, animal_vars[i] == cat_idx))
    
    # Clue 6: Horse owner is the teacher
    horse_idx = animal_to_idx['horse']
    teacher_idx = occupation_to_idx['teacher']
    for i in range(6):
        solver.add(Implies(animal_vars[i] == horse_idx, occupation_vars[i] == teacher_idx))
    
    # Clue 7: Carol loves soccer
    carol_idx = name_to_idx['Carol']
    soccer_idx = sport_to_idx['soccer']
    for i in range(6):
        solver.add(Implies(name_vars[i] == carol_idx, sport_vars[i] == soccer_idx))
    
    # Clue 8: Tall height loves volleyball
    volleyball_idx = sport_to_idx['volleyball']
    for i in range(6):
        solver.add(Implies(height_vars[i] == tall_idx, sport_vars[i] == volleyball_idx))
    
    # Clue 9: Lawyer is in the fifth house
    lawyer_idx = occupation_to_idx['lawyer']
    solver.add(occupation_vars[4] == lawyer_idx)
    
    # Clue 10: Tennis lover is the teacher
    tennis_idx = sport_to_idx['tennis']
    for i in range(6):
        solver.add(Implies(sport_vars[i] == tennis_idx, occupation_vars[i] == teacher_idx))
    
    # Clue 11: Average height loves swimming
    swimming_idx = sport_to_idx['swimming']
    for i in range(6):
        solver.add(Implies(height_vars[i] == avg_idx, sport_vars[i] == swimming_idx))
    
    # Clue 12: Baseball lover is directly left of the engineer
    baseball_idx = sport_to_idx['baseball']
    solver.add(Or([And(sport_vars[i] == baseball_idx, occupation_vars[i+1] == engineer_idx) for i in range(5)]))
    
    # Clue 13: Peter is the nurse
    peter_idx = name_to_idx['Peter']
    nurse_idx = occupation_to_idx['nurse']
    for i in range(6):
        solver.add(Implies(name_vars[i] == peter_idx, occupation_vars[i] == nurse_idx))
    
    # Clue 14: Bob is right of the artist
    bob_idx = name_to_idx['Bob']
    artist_idx = occupation_to_idx['artist']
    artist_house = Int('artist_house')
    bob_house = Int('bob_house')
    solver.add(artist_house >= 0, artist_house < 6)
    solver.add(bob_house >= 0, bob_house < 6)
    solver.add(Or([And(artist_house == i, occupation_vars[i] == artist_idx) for i in range(6)]))
    solver.add(Or([And(bob_house == i, name_vars[i] == bob_idx) for i in range(6)]))
    solver.add(artist_house < bob_house)
    
    # Clue 15: Teacher is directly left of soccer lover
    solver.add(Or([And(occupation_vars[i] == teacher_idx, sport_vars[i+1] == soccer_idx) for i in range(5)]))
    
    # Clue 16: Rabbit owner is Alice
    alice_idx = name_to_idx['Alice']
    for i in range(6):
        solver.add(Implies(animal_vars[i] == rabbit_idx, name_vars[i] == alice_idx))
    
    # Clue 17: Fish enthusiast is Carol
    fish_idx = animal_to_idx['fish']
    for i in range(6):
        solver.add(Implies(animal_vars[i] == fish_idx, name_vars[i] == carol_idx))
    
    # Clue 18: Baseball lover is in the first house
    solver.add(sport_vars[0] == baseball_idx)
    
    # Clue 19: Cat owner is right of very short height
    very_short_house = Int('very_short_house')
    cat_house = Int('cat_house')
    solver.add(very_short_house >= 0, very_short_house < 6)
    solver.add(cat_house >= 0, cat_house < 6)
    solver.add(Or([And(very_short_house == i, height_vars[i] == very_short_idx) for i in range(6)]))
    solver.add(Or([And(cat_house == i, animal_vars[i] == cat_idx) for i in range(6)]))
    solver.add(very_short_house < cat_house)
    
    # Clue 20: Super tall is in the fifth house
    super_tall_idx = height_to_idx['super tall']
    solver.add(height_vars[4] == super_tall_idx)
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for i in range(6):
            house = i + 1
            name_val = names[model.evaluate(name_vars[i]).as_long()]
            animal_val = animals[model.evaluate(animal_vars[i]).as_long()]
            occupation_val = occupations[model.evaluate(occupation_vars[i]).as_long()]
            sport_val = sports[model.evaluate(sport_vars[i]).as_long()]
            height_val = heights[model.evaluate(height_vars[i]).as_long()]
            solution.append([str(house), name_val, animal_val, occupation_val, sport_val, height_val])
        
        # Format the solution as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
                "rows": solution
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    import json
    main()