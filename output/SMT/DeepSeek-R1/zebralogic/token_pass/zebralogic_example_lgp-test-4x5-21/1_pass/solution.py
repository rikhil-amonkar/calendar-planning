import z3
import json

def main():
    # Initialize the solver
    solver = z3.Solver()
    
    # Number of houses
    n_houses = 4
    
    # Attributes and their possible values
    names = ['Eric', 'Alice', 'Peter', 'Arnold']
    smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    sports = ['soccer', 'tennis', 'basketball', 'swimming']
    car_models = ['tesla model 3', 'toyota camry', 'honda civic', 'ford f150']
    flowers = ['daffodils', 'roses', 'lilies', 'carnations']
    
    # Create Z3 variables for each attribute in each house
    name_vars = [z3.Int(f"name_{i}") for i in range(n_houses)]
    smoothie_vars = [z3.Int(f"smoothie_{i}") for i in range(n_houses)]
    sport_vars = [z3.Int(f"sport_{i}") for i in range(n_houses)]
    car_vars = [z3.Int(f"car_{i}") for i in range(n_houses)]
    flower_vars = [z3.Int(f"flower_{i}") for i in range(n_houses)]
    
    # Add constraints: each attribute must be between 0 and 3 (index of the value)
    for i in range(n_houses):
        solver.add(z3.And(name_vars[i] >= 0, name_vars[i] < 4))
        solver.add(z3.And(smoothie_vars[i] >= 0, smoothie_vars[i] < 4))
        solver.add(z3.And(sport_vars[i] >= 0, sport_vars[i] < 4))
        solver.add(z3.And(car_vars[i] >= 0, car_vars[i] < 4))
        solver.add(z3.And(flower_vars[i] >= 0, flower_vars[i] < 4))
    
    # Each set of attributes must have distinct values
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(smoothie_vars))
    solver.add(z3.Distinct(sport_vars))
    solver.add(z3.Distinct(car_vars))
    solver.add(z3.Distinct(flower_vars))
    
    # Clue 1: Tesla Model 3 owner loves roses
    for i in range(n_houses):
        solver.add(z3.Implies(car_vars[i] == car_models.index('tesla model 3'), 
                              flower_vars[i] == flowers.index('roses')))
    
    # Clue 2: Peter loves dragonfruit smoothie
    for i in range(n_houses):
        solver.add(z3.Implies(name_vars[i] == names.index('Peter'), 
                              smoothie_vars[i] == smoothies.index('dragonfruit')))
    
    # Clue 3: Desert smoothie lover owns Toyota Camry
    for i in range(n_houses):
        solver.add(z3.Implies(smoothie_vars[i] == smoothies.index('desert'), 
                              car_vars[i] == car_models.index('toyota camry')))
    
    # Clue 4: Tennis lover in first house
    solver.add(sport_vars[0] == sports.index('tennis'))
    
    # Clue 5: Toyota Camry owner and basketball lover are adjacent
    for i in range(n_houses):
        if i > 0:
            solver.add(z3.Implies(car_vars[i] == car_models.index('toyota camry'),
                                  z3.Or(sport_vars[i-1] == sports.index('basketball'))))
        if i < n_houses - 1:
            solver.add(z3.Implies(car_vars[i] == car_models.index('toyota camry'),
                                  z3.Or(sport_vars[i+1] == sports.index('basketball'))))
        if i > 0:
            solver.add(z3.Implies(sport_vars[i] == sports.index('basketball'),
                                  z3.Or(car_vars[i-1] == car_models.index('toyota camry'))))
        if i < n_houses - 1:
            solver.add(z3.Implies(sport_vars[i] == sports.index('basketball'),
                                  z3.Or(car_vars[i+1] == car_models.index('toyota camry'))))
    
    # Clue 6: Arnold loves basketball
    for i in range(n_houses):
        solver.add(z3.Implies(name_vars[i] == names.index('Arnold'), 
                              sport_vars[i] == sports.index('basketball')))
    
    # Clue 7: Honda Civic owner loves daffodils
    for i in range(n_houses):
        solver.add(z3.Implies(car_vars[i] == car_models.index('honda civic'), 
                              flower_vars[i] == flowers.index('daffodils')))
    
    # Clue 8: Eric loves roses
    for i in range(n_houses):
        solver.add(z3.Implies(name_vars[i] == names.index('Eric'), 
                              flower_vars[i] == flowers.index('roses')))
    
    # Clue 9: Watermelon smoothie not in first house
    solver.add(smoothie_vars[0] != smoothies.index('watermelon'))
    
    # Clue 10: Honda Civic owner right of Desert smoothie lover
    desert_smoothie_index = smoothies.index('desert')
    honda_civic_index = car_models.index('honda civic')
    for i in range(n_houses):
        for j in range(n_houses):
            if i < j:
                solver.add(z3.Implies(z3.And(smoothie_vars[i] == desert_smoothie_index, car_vars[j] == honda_civic_index), True))
            else:
                solver.add(z3.Not(z3.And(smoothie_vars[i] == desert_smoothie_index, car_vars[j] == honda_civic_index)))
    
    # Clue 11: Basketball lover loves lilies
    for i in range(n_houses):
        solver.add(z3.Implies(sport_vars[i] == sports.index('basketball'), 
                              flower_vars[i] == flowers.index('lilies')))
    
    # Clue 12: Tennis and soccer lovers are adjacent
    tennis_index = sports.index('tennis')
    soccer_index = sports.index('soccer')
    for i in range(n_houses):
        if i > 0:
            solver.add(z3.Implies(sport_vars[i] == tennis_index,
                                  z3.Or(sport_vars[i-1] == soccer_index)))
        if i < n_houses - 1:
            solver.add(z3.Implies(sport_vars[i] == tennis_index,
                                  z3.Or(sport_vars[i+1] == soccer_index)))
        if i > 0:
            solver.add(z3.Implies(sport_vars[i] == soccer_index,
                                  z3.Or(sport_vars[i-1] == tennis_index)))
        if i < n_houses - 1:
            solver.add(z3.Implies(sport_vars[i] == soccer_index,
                                  z3.Or(sport_vars[i+1] == tennis_index)))
    
    # Check if the solver is satisfied and get the solution
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Create result arrays
        result = []
        for i in range(n_houses):
            name_val = model.eval(name_vars[i]).as_long()
            smoothie_val = model.eval(smoothie_vars[i]).as_long()
            sport_val = model.eval(sport_vars[i]).as_long()
            car_val = model.eval(car_vars[i]).as_long()
            flower_val = model.eval(flower_vars[i]).as_long()
            
            row = [
                str(i+1),
                names[name_val],
                smoothies[smoothie_val],
                sports[sport_val],
                car_models[car_val],
                flowers[flower_val]
            ]
            result.append(row)
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()