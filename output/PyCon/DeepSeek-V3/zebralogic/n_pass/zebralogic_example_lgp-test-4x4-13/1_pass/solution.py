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
    problem.addVariables(["name"], names)
    problem.addVariables(["cigar"], cigars)
    problem.addVariables(["sport"], sports)
    problem.addVariables(["drink"], drinks)
    
    # All attributes must be different
    problem.addConstraint(AllDifferentConstraint(), ["name"])
    problem.addConstraint(AllDifferentConstraint(), ["cigar"])
    problem.addConstraint(AllDifferentConstraint(), ["sport"])
    problem.addConstraint(AllDifferentConstraint(), ["drink"])
    
    # Clue 1: Peter is in the fourth house
    problem.addConstraint(lambda name: name == 'Peter', ['name_4'])
    
    # Clue 2: The tea drinker is the person who loves basketball
    problem.addConstraint(lambda drink, sport: (drink == 'tea') == (sport == 'basketball'), ['drink', 'sport'])
    
    # Clue 3: Arnold is the person who smokes Blue Master
    problem.addConstraint(lambda name, cigar: (name == 'Arnold') == (cigar == 'blue master'), ['name', 'cigar'])
    
    # Clue 4: The person who loves basketball is Eric
    problem.addConstraint(lambda sport, name: (sport == 'basketball') == (name == 'Eric'), ['sport', 'name'])
    
    # Clue 5: The person who loves tennis is the person who smokes Blue Master
    problem.addConstraint(lambda sport, cigar: (sport == 'tennis') == (cigar == 'blue master'), ['sport', 'cigar'])
    
    # Clue 6: There are two houses between the one who only drinks water and Peter
    # Peter is in house 4, so water drinker must be in house 1
    problem.addConstraint(lambda drink: drink == 'water', ['drink_1'])
    
    # Clue 7: The coffee drinker is Arnold
    problem.addConstraint(lambda drink, name: (drink == 'coffee') == (name == 'Arnold'), ['drink', 'name'])
    
    # Clue 8: The person who loves basketball is in the third house
    problem.addConstraint(lambda sport: sport == 'basketball', ['sport_3'])
    
    # Clue 9: The Prince smoker is the person who loves soccer
    problem.addConstraint(lambda cigar, sport: (cigar == 'prince') == (sport == 'soccer'), ['cigar', 'sport'])
    
    # Clue 10: Peter is the person partial to Pall Mall
    problem.addConstraint(lambda name, cigar: (name == 'Peter') == (cigar == 'pall mall'), ['name', 'cigar'])
    
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