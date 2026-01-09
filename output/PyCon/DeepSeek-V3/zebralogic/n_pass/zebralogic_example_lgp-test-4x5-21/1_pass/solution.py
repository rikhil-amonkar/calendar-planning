from constraint import Problem
import json

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4]
    
    # Define variables
    names = ['Eric', 'Alice', 'Peter', 'Arnold']
    smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    sports = ['soccer', 'tennis', 'basketball', 'swimming']
    cars = ['tesla model 3', 'toyota camry', 'honda civic', 'ford f150']
    flowers = ['daffodils', 'roses', 'lilies', 'carnations']
    
    # Add variables for each category
    problem.addVariables(['name1', 'name2', 'name3', 'name4'], names)
    problem.addVariables(['smoothie1', 'smoothie2', 'smoothie3', 'smoothie4'], smoothies)
    problem.addVariables(['sport1', 'sport2', 'sport3', 'sport4'], sports)
    problem.addVariables(['car1', 'car2', 'car3', 'car4'], cars)
    problem.addVariables(['flower1', 'flower2', 'flower3', 'flower4'], flowers)
    
    # All variables must have different values within their category
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         ['name1', 'name2', 'name3', 'name4'])
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         ['smoothie1', 'smoothie2', 'smoothie3', 'smoothie4'])
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         ['sport1', 'sport2', 'sport3', 'sport4'])
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         ['car1', 'car2', 'car3', 'car4'])
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         ['flower1', 'flower2', 'flower3', 'flower4'])
    
    # Clue 1: Tesla Model 3 owner loves roses
    for i in houses:
        problem.addConstraint(lambda car, flower, house=i: 
                             not (car == 'tesla model 3') or (flower == 'roses'),
                             [f'car{house}', f'flower{house}'])
    
    # Clue 2: Peter loves dragonfruit smoothie
    for i in houses:
        problem.addConstraint(lambda name, smoothie, house=i: 
                             not (name == 'Peter') or (smoothie == 'dragonfruit'),
                             [f'name{house}', f'smoothie{house}'])
    
    # Clue 3: Desert smoothie lover owns Toyota Camry
    for i in houses:
        problem.addConstraint(lambda smoothie, car, house=i: 
                             not (smoothie == 'desert') or (car == 'toyota camry'),
                             [f'smoothie{house}', f'car{house}'])
    
    # Clue 4: Tennis lover is in first house
    problem.addConstraint(lambda sport: sport == 'tennis', ['sport1'])
    
    # Clue 5: Toyota Camry owner and basketball lover are next to each other
    def adjacent_car_sport(car1, car2, car3, car4, sport1, sport2, sport3, sport4):
        basketball_houses = []
        toyota_houses = []
        
        if sport1 == 'basketball': basketball_houses.append(1)
        if sport2 == 'basketball': basketball_houses.append(2)
        if sport3 == 'basketball': basketball_houses.append(3)
        if sport4 == 'basketball': basketball_houses.append(4)
        
        if car1 == 'toyota camry': toyota_houses.append(1)
        if car2 == 'toyota camry': toyota_houses.append(2)
        if car3 == 'toyota camry': toyota_houses.append(3)
        if car4 == 'toyota camry': toyota_houses.append(4)
        
        for b in basketball_houses:
            for t in toyota_houses:
                if abs(b - t) == 1:
                    return True
        return False
    
    problem.addConstraint(adjacent_car_sport, 
                         ['car1', 'car2', 'car3', 'car4', 'sport1', 'sport2', 'sport3', 'sport4'])
    
    # Clue 6: Arnold loves basketball
    for i in houses:
        problem.addConstraint(lambda name, sport, house=i: 
                             not (name == 'Arnold') or (sport == 'basketball'),
                             [f'name{house}', f'sport{house}'])
    
    # Clue 7: Honda Civic owner loves daffodils
    for i in houses:
        problem.addConstraint(lambda car, flower, house=i: 
                             not (car == 'honda civic') or (flower == 'daffodils'),
                             [f'car{house}', f'flower{house}'])
    
    # Clue 8: Eric loves roses
    for i in houses:
        problem.addConstraint(lambda name, flower, house=i: 
                             not (name == 'Eric') or (flower == 'roses'),
                             [f'name{house}', f'flower{house}'])
    
    # Clue 9: Watermelon smoothie lover not in first house
    problem.addConstraint(lambda smoothie: smoothie != 'watermelon', ['smoothie1'])
    
    # Clue 10: Honda Civic owner is to the right of Desert smoothie lover
    def honda_right_of_desert(smoothie1, smoothie2, smoothie3, smoothie4, 
                             car1, car2, car3, car4):
        desert_house = None
        honda_house = None
        
        if smoothie1 == 'desert': desert_house = 1
        if smoothie2 == 'desert': desert_house = 2
        if smoothie3 == 'desert': desert_house = 3
        if smoothie4 == 'desert': desert_house = 4
        
        if car1 == 'honda civic': honda_house = 1
        if car2 == 'honda civic': honda_house = 2
        if car3 == 'honda civic': honda_house = 3
        if car4 == 'honda civic': honda_house = 4
        
        return honda_house > desert_house
    
    problem.addConstraint(honda_right_of_desert, 
                         ['smoothie1', 'smoothie2', 'smoothie3', 'smoothie4',
                          'car1', 'car2', 'car3', 'car4'])
    
    # Clue 11: Basketball lover loves lilies
    for i in houses:
        problem.addConstraint(lambda sport, flower, house=i: 
                             not (sport == 'basketball') or (flower == 'lilies'),
                             [f'sport{house}', f'flower{house}'])
    
    # Clue 12: Tennis and soccer lovers are next to each other
    def adjacent_tennis_soccer(sport1, sport2, sport3, sport4):
        tennis_house = None
        soccer_house = None
        
        if sport1 == 'tennis': tennis_house = 1
        if sport2 == 'tennis': tennis_house = 2
        if sport3 == 'tennis': tennis_house = 3
        if sport4 == 'tennis': tennis_house = 4
        
        if sport1 == 'soccer': soccer_house = 1
        if sport2 == 'soccer': soccer_house = 2
        if sport3 == 'soccer': soccer_house = 3
        if sport4 == 'soccer': soccer_house = 4
        
        return abs(tennis_house - soccer_house) == 1
    
    problem.addConstraint(adjacent_tennis_soccer, 
                         ['sport1', 'sport2', 'sport3', 'sport4'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    header = ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"]
    rows = []
    
    for house in houses:
        row = [
            str(house),
            solution[f'name{house}'],
            solution[f'smoothie{house}'],
            solution[f'sport{house}'],
            solution[f'car{house}'],
            solution[f'flower{house}']
        ]
        rows.append(row)
    
    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))