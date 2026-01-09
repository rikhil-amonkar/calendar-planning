import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each attribute
    names = ['Alice', 'Peter', 'Arnold', 'Eric']
    cigars = ['prince', 'dunhill', 'blue master', 'pall mall']
    sports = ['swimming', 'basketball', 'soccer', 'tennis']
    drinks = ['coffee', 'water', 'milk', 'tea']
    
    houses = [1, 2, 3, 4]
    
    # Add variables for each attribute per house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"cigar_{house}", cigars)
        problem.addVariable(f"sport_{house}", sports)
        problem.addVariable(f"drink_{house}", drinks)
    
    # All attributes must be different across houses
    problem.addConstraint(AllDifferentConstraint(), [f"name_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"cigar_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"sport_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"drink_{h}" for h in houses])
    
    # Clue 1: Peter is in the fourth house
    problem.addConstraint(lambda name_4: name_4 == 'Peter', ['name_4'])
    
    # Clue 2: The tea drinker is the person who loves basketball
    for house in houses:
        problem.addConstraint(lambda drink, sport: (drink == 'tea') == (sport == 'basketball'), 
                            [f'drink_{house}', f'sport_{house}'])
    
    # Clue 3: Arnold is the person who smokes Blue Master
    for house in houses:
        problem.addConstraint(lambda name, cigar: (name == 'Arnold') == (cigar == 'blue master'), 
                            [f'name_{house}', f'cigar_{house}'])
    
    # Clue 4: The person who loves basketball is Eric
    for house in houses:
        problem.addConstraint(lambda sport, name: (sport == 'basketball') == (name == 'Eric'), 
                            [f'sport_{house}', f'name_{house}'])
    
    # Clue 5: The person who loves tennis is the person who smokes Blue Master
    for house in houses:
        problem.addConstraint(lambda sport, cigar: (sport == 'tennis') == (cigar == 'blue master'), 
                            [f'sport_{house}', f'cigar_{house}'])
    
    # Clue 6: There are two houses between the one who only drinks water and Peter
    # Peter is in house 4, so water drinker must be in house 1
    problem.addConstraint(lambda drink_1: drink_1 == 'water', ['drink_1'])
    
    # Clue 7: The coffee drinker is Arnold
    for house in houses:
        problem.addConstraint(lambda drink, name: (drink == 'coffee') == (name == 'Arnold'), 
                            [f'drink_{house}', f'name_{house}'])
    
    # Clue 8: The person who loves basketball is in the third house
    problem.addConstraint(lambda sport_3: sport_3 == 'basketball', ['sport_3'])
    
    # Clue 9: The Prince smoker is the person who loves soccer
    for house in houses:
        problem.addConstraint(lambda cigar, sport: (cigar == 'prince') == (sport == 'soccer'), 
                            [f'cigar_{house}', f'sport_{house}'])
    
    # Clue 10: Peter is the person partial to Pall Mall
    for house in houses:
        problem.addConstraint(lambda name, cigar: (name == 'Peter') == (cigar == 'pall mall'), 
                            [f'name_{house}', f'cigar_{house}'])
    
    # Get all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"], "rows": []}}
    
    # Convert solution to the required format
    solution = solutions[0]
    
    rows = []
    for house in houses:
        name = solution[f'name_{house}']
        cigar = solution[f'cigar_{house}']
        sport = solution[f'sport_{house}']
        drink = solution[f'drink_{house}']
        rows.append([str(house), name, cigar, sport, drink])
    
    return {
        "solution": {
            "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))