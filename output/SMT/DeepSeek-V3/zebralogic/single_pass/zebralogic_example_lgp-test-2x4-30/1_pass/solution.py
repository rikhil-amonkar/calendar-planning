from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    solver = Solver()

    # Define the houses
    houses = [1, 2]

    # Define the attributes
    names = {'Arnold', 'Eric'}
    hair_colors = {'black', 'brown'}
    sports = {'basketball', 'soccer'}
    smoothies = {'desert', 'cherry'}

    # Create variables for each attribute in each house
    name = {house: String(f'name_{house}') for house in houses}
    hair_color = {house: String(f'hair_color_{house}') for house in houses}
    favorite_sport = {house: String(f'favorite_sport_{house}') for house in houses}
    smoothie = {house: String(f'smoothie_{house}') for house in houses}

    # Add constraints for uniqueness of each attribute
    solver.add(Distinct([name[house] for house in houses]))
    solver.add(Distinct([hair_color[house] for house in houses]))
    solver.add(Distinct([favorite_sport[house] for house in houses]))
    solver.add(Distinct([smoothie[house] for house in houses]))

    # Each attribute must be one of the allowed values
    for house in houses:
        solver.add(Or([name[house] == n for n in names]))
        solver.add(Or([hair_color[house] == h for h in hair_colors]))
        solver.add(Or([favorite_sport[house] == s for s in sports]))
        solver.add(Or([smoothie[house] == sm for sm in smoothies]))

    # Apply the clues
    # Clue 1: The Desert smoothie lover is Arnold.
    for house in houses:
        solver.add(Implies(smoothie[house] == 'desert', name[house] == 'Arnold'))

    # Clue 2: The person who has brown hair is the person who loves basketball.
    for house in houses:
        solver.add(Implies(hair_color[house] == 'brown', favorite_sport[house] == 'basketball'))
        solver.add(Implies(favorite_sport[house] == 'basketball', hair_color[house] == 'brown'))

    # Clue 3: Arnold is somewhere to the left of the person who has black hair.
    # This means Arnold is in house 1 and black hair is in house 2, or Arnold is in house 1 and black hair is in house 2 (only possible arrangement)
    solver.add(Or(
        And(name[1] == 'Arnold', hair_color[2] == 'black'),
        And(name[1] == 'Arnold', hair_color[2] == 'black')  # Redundant but ensures the constraint
    ))

    # Since there are only two houses, the above simplifies to Arnold in 1 and black hair in 2
    solver.add(name[1] == 'Arnold')
    solver.add(hair_color[2] == 'black')

    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
                "rows": []
            }
        }
        for house in sorted(houses):
            row = [
                str(house),
                model.evaluate(name[house]).as_string(),
                model.evaluate(hair_color[house]).as_string(),
                model.evaluate(favorite_sport[house]).as_string(),
                model.evaluate(smoothie[house]).as_string()
            ]
            solution["solution"]["rows"].append(row)
        return solution
    else:
        return {"error": "No solution found"}

# Get the solution
solution = solve_scheduling_problem()

# Print the solution as JSON
import json
print(json.dumps(solution, indent=2))