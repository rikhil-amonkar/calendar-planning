import json
from z3 import *

def main():
    # Initialize solver
    solver = Solver()
    
    # Define attributes
    names = ['Eric', 'Alice', 'Peter', 'Arnold']
    smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    sports = ['soccer', 'tennis', 'basketball', 'swimming']
    cars = ['tesla model 3', 'toyota camry', 'honda civic', 'ford f150']
    flowers = ['daffodils', 'roses', 'lilies', 'carnations']
    
    # Create house assignment variables for each attribute
    name_vars = {n: Int(f"{n}_house") for n in names}
    smoothie_vars = {s: Int(f"{s}_house") for s in smoothies}
    sport_vars = {s: Int(f"{s}_house") for s in sports}
    car_vars = {c: Int(f"{c}_house") for c in cars}
    flower_vars = {f: Int(f"{f}_house") for f in flowers}
    
    # All house assignments must be between 1 and 4
    for var_dict in [name_vars, smoothie_vars, sport_vars, car_vars, flower_vars]:
        for v in var_dict.values():
            solver.add(v >= 1, v <= 4)
    
    # All attributes in each category must be in different houses
    for var_dict in [name_vars, smoothie_vars, sport_vars, car_vars, flower_vars]:
        solver.add(Distinct([v for v in var_dict.values()]))
    
    # Add clues
    # 1. Tesla Model 3 owner loves roses
    solver.add(car_vars['tesla model 3'] == flower_vars['roses'])
    
    # 2. Peter loves dragonfruit smoothie
    solver.add(name_vars['Peter'] == smoothie_vars['dragonfruit'])
    
    # 3. Desert smoothie lover owns Toyota Camry
    solver.add(smoothie_vars['desert'] == car_vars['toyota camry'])
    
    # 4. Tennis lover in first house
    solver.add(sport_vars['tennis'] == 1)
    
    # 5. Toyota Camry owner and basketball lover are adjacent
    solver.add(Abs(car_vars['toyota camry'] - sport_vars['basketball']) == 1)
    
    # 6. Arnold loves basketball
    solver.add(name_vars['Arnold'] == sport_vars['basketball'])
    
    # 7. Honda Civic owner loves daffodils
    solver.add(car_vars['honda civic'] == flower_vars['daffodils'])
    
    # 8. Eric loves roses
    solver.add(name_vars['Eric'] == flower_vars['roses'])
    
    # 9. Watermelon smoothie not in first house
    solver.add(smoothie_vars['watermelon'] != 1)
    
    # 10. Honda Civic owner right of Desert smoothie lover
    solver.add(car_vars['honda civic'] > smoothie_vars['desert'])
    
    # 11. Basketball lover loves lilies
    solver.add(sport_vars['basketball'] == flower_vars['lilies'])
    
    # 12. Tennis and soccer lovers are adjacent
    solver.add(Abs(sport_vars['tennis'] - sport_vars['soccer']) == 1)
    
    # Check solution
    if solver.check() == sat:
        model = solver.model()
        
        # Create reverse mapping from house numbers to attributes
        house_assignments = {}
        for house in range(1, 5):
            house_assignments[house] = {
                'Name': next(n for n, v in name_vars.items() if model.eval(v).as_long() == house),
                'Smoothie': next(s for s, v in smoothie_vars.items() if model.eval(v).as_long() == house),
                'FavoriteSport': next(s for s, v in sport_vars.items() if model.eval(v).as_long() == house),
                'CarModel': next(c for c, v in car_vars.items() if model.eval(v).as_long() == house),
                'Flower': next(f for f, v in flower_vars.items() if model.eval(v).as_long() == house)
            }
        
        # Build output JSON
        header = ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"]
        rows = []
        for house in range(1, 5):
            attr = house_assignments[house]
            rows.append([
                str(house),
                attr['Name'],
                attr['Smoothie'],
                attr['FavoriteSport'],
                attr['CarModel'],
                attr['Flower']
            ])
        
        output = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()