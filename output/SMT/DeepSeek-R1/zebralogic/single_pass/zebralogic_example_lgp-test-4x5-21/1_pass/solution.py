from z3 import *

def main():
    # Define the attribute lists and their indices
    name_list = ['Eric', 'Alice', 'Peter', 'Arnold']
    smoothie_list = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    sport_list = ['soccer', 'tennis', 'basketball', 'swimming']
    car_list = ['tesla model 3', 'toyota camry', 'honda civic', 'ford f150']
    flower_list = ['daffodils', 'roses', 'lilies', 'carnations']
    
    # Assign indices for clarity
    Eric_idx = 0
    Alice_idx = 1
    Peter_idx = 2
    Arnold_idx = 3
    
    dragonfruit_idx = 0
    cherry_idx = 1
    desert_idx = 2
    watermelon_idx = 3
    
    soccer_idx = 0
    tennis_idx = 1
    basketball_idx = 2
    swimming_idx = 3
    
    tesla_idx = 0
    toyota_idx = 1
    honda_idx = 2
    ford_idx = 3
    
    daffodils_idx = 0
    roses_idx = 1
    lilies_idx = 2
    carnations_idx = 3

    # Create Z3 variables for attributes of each house
    names = [Int('name_%d' % i) for i in range(4)]
    smoothies = [Int('smoothie_%d' % i) for i in range(4)]
    sports = [Int('sport_%d' % i) for i in range(4)]
    cars = [Int('car_%d' % i) for i in range(4)]
    flowers = [Int('flower_%d' % i) for i in range(4)]
    
    s = Solver()
    
    # Ensure all attributes are within 0-3
    for i in range(4):
        s.add(And(names[i] >= 0, names[i] <= 3))
        s.add(And(smoothies[i] >= 0, smoothies[i] <= 3))
        s.add(And(sports[i] >= 0, sports[i] <= 3))
        s.add(And(cars[i] >= 0, cars[i] <= 3))
        s.add(And(flowers[i] >= 0, flowers[i] <= 3))
    
    # Distinct constraints
    s.add(Distinct(names))
    s.add(Distinct(smoothies))
    s.add(Distinct(sports))
    s.add(Distinct(cars))
    s.add(Distinct(flowers))
    
    # Clue 4: Tennis in first house
    s.add(sports[0] == tennis_idx)
    
    # Clue 12: Tennis and soccer are adjacent; since tennis is in house1, soccer must be in house2
    s.add(sports[1] == soccer_idx)
    
    # Clue 9: Watermelon smoothie not in first house
    s.add(smoothies[0] != watermelon_idx)
    
    # Clue 2: Peter loves dragonfruit
    for i in range(4):
        s.add(Implies(names[i] == Peter_idx, smoothies[i] == dragonfruit_idx))
    
    # Clue 3: Desert smoothie lover owns Toyota Camry
    for i in range(4):
        s.add((smoothies[i] == desert_idx) == (cars[i] == toyota_idx))
    
    # Clue 6: Arnold loves basketball
    for i in range(4):
        s.add(Implies(names[i] == Arnold_idx, sports[i] == basketball_idx))
    
    # Clue 11: Basketball lover loves lilies
    for i in range(4):
        s.add((sports[i] == basketball_idx) == (flowers[i] == lilies_idx))
    
    # Clue 1: Tesla Model 3 owner loves roses
    for i in range(4):
        s.add((cars[i] == tesla_idx) == (flowers[i] == roses_idx))
    
    # Clue 7: Honda Civic owner loves daffodils
    for i in range(4):
        s.add((cars[i] == honda_idx) == (flowers[i] == daffodils_idx))
    
    # Clue 8: Eric loves roses
    for i in range(4):
        s.add(Implies(names[i] == Eric_idx, flowers[i] == roses_idx))
    
    # Clue 5: Toyota Camry owner and basketball lover are adjacent
    for i in range(4):
        s.add(Implies(sports[i] == basketball_idx, 
                      Or(And(i > 0, cars[i-1] == toyota_idx), 
                         And(i < 3, cars[i+1] == toyota_idx))))
    
    # Clue 10: Honda Civic owner is to the right of Desert smoothie lover
    desert_sum = Sum([If(smoothies[i] == desert_idx, i, 0) for i in range(4)])
    honda_sum = Sum([If(cars[i] == honda_idx, i, 0) for i in range(4)])
    s.add(honda_sum > desert_sum)
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(4):
            name_val = m.evaluate(names[i]).as_long()
            smoothie_val = m.evaluate(smoothies[i]).as_long()
            sport_val = m.evaluate(sports[i]).as_long()
            car_val = m.evaluate(cars[i]).as_long()
            flower_val = m.evaluate(flowers[i]).as_long()
            
            row = [
                str(i+1),
                name_list[name_val],
                smoothie_list[smoothie_val],
                sport_list[sport_val],
                car_list[car_val],
                flower_list[flower_val]
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
                "rows": rows
            }
        }
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()