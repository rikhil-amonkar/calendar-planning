import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1, 2, 3)
    houses = [1, 2, 3]
    
    # Define domains for each attribute
    names = ['Eric', 'Peter', 'Arnold']
    cigars = ['blue master', 'prince', 'pall mall']
    hobbies = ['photography', 'gardening', 'cooking']
    educations = ['high school', 'associate', 'bachelor']
    drinks = ['tea', 'milk', 'water']
    
    # Add variables for each attribute per house
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'cigar_{house}', cigars)
        problem.addVariable(f'hobby_{house}', hobbies)
        problem.addVariable(f'education_{house}', educations)
        problem.addVariable(f'drink_{house}', drinks)
    
    # All attributes must be different across houses
    for attr in ['name', 'cigar', 'hobby', 'education', 'drink']:
        problem.addConstraint(AllDifferentConstraint(), [f'{attr}_{house}' for house in houses])
    
    # Clue 1: The person partial to Pall Mall is Peter.
    for house in houses:
        problem.addConstraint(
            lambda cigar, name: not (cigar == 'pall mall') or (name == 'Peter'),
            [f'cigar_{house}', f'name_{house}']
        )
    
    # Clue 2: The person who likes milk is directly left of the person with a high school diploma.
    for i in range(1, 3):
        problem.addConstraint(
            lambda drink1, education2: not (drink1 == 'milk') or (education2 == 'high school'),
            [f'drink_{i}', f'education_{i+1}']
        )
    
    # Clue 3: Eric is the tea drinker.
    for house in houses:
        problem.addConstraint(
            lambda name, drink: not (name == 'Eric') or (drink == 'tea'),
            [f'name_{house}', f'drink_{house}']
        )
    
    # Clue 4: Arnold and the Prince smoker are next to each other.
    def are_adjacent(arnold_house, prince_house):
        return abs(arnold_house - prince_house) == 1
    
    # Find Arnold's house and Prince smoker's house
    arnold_house_vars = []
    prince_house_vars = []
    for house in houses:
        arnold_house_vars.append((house, f'name_{house}'))
        prince_house_vars.append((house, f'cigar_{house}'))
    
    # Create constraints for adjacency
    for (h1, var1) in arnold_house_vars:
        for (h2, var2) in prince_house_vars:
            problem.addConstraint(
                lambda name, cigar: not (name == 'Arnold' and cigar == 'prince') or are_adjacent(h1, h2),
                [var1, var2]
            )
    
    # Clue 5: The person who enjoys gardening is somewhere to the left of the Prince smoker.
    def is_left(gardening_house, prince_house):
        return gardening_house < prince_house
    
    # Find gardening hobby house and Prince smoker house
    gardening_house_vars = []
    prince_house_vars = []
    for house in houses:
        gardening_house_vars.append((house, f'hobby_{house}'))
        prince_house_vars.append((house, f'cigar_{house}'))
    
    # Create constraints for left position
    for (h1, var1) in gardening_house_vars:
        for (h2, var2) in prince_house_vars:
            problem.addConstraint(
                lambda hobby, cigar: not (hobby == 'gardening' and cigar == 'prince') or is_left(h1, h2),
                [var1, var2]
            )
    
    # Clue 6: The person who likes milk is the person with an associate's degree.
    for house in houses:
        problem.addConstraint(
            lambda drink, education: not (drink == 'milk') or (education == 'associate'),
            [f'drink_{house}', f'education_{house}']
        )
    
    # Clue 7: The person with a bachelor's degree is directly left of the photography enthusiast.
    for i in range(1, 3):
        problem.addConstraint(
            lambda education1, hobby2: not (education1 == 'bachelor') or (hobby2 == 'photography'),
            [f'education_{i}', f'hobby_{i+1}']
        )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result structure
    header = ["House", "Name", "Cigar", "Hobby", "Education", "Drink"]
    rows = []
    
    for house in houses:
        row = [
            str(house),
            solution[f'name_{house}'],
            solution[f'cigar_{house}'],
            solution[f'hobby_{house}'],
            solution[f'education_{house}'],
            solution[f'drink_{house}']
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))