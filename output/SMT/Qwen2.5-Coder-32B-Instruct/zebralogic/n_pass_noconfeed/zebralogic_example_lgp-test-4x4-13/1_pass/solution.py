from z3 import *

def solve_puzzle():
    # Define the domains
    houses = [1, 2, 3, 4]
    names = ["Alice", "Peter", "Arnold", "Eric"]
    cigars = ["prince", "dunhill", "blue master", "pall mall"]
    sports = ["swimming", "basketball", "soccer", "tennis"]
    drinks = ["coffee", "water", "milk", "tea"]

    # Create dictionaries to map variables to Z3 variables
    name_vars = {house: Int(f"name_{house}") for house in houses}
    cigar_vars = {house: Int(f"cigar_{house}") for house in houses}
    sport_vars = {house: Int(f"sport_{house}") for house in houses}
    drink_vars = {house: Int(f"drink_{house}") for house in houses}

    # Create a solver instance
    solver = Solver()

    # Add constraints for unique values per category
    for var_dict, domain in [(name_vars, names), (cigar_vars, cigars), (sport_vars, sports), (drink_vars, drinks)]:
        solver.add(Distinct([var_dict[house] for house in houses]))
        for house in houses:
            solver.add(var_dict[house] >= 0)
            solver.add(var_dict[house] < len(domain))

    # Add specific clues as constraints
    # 1. Peter is in the fourth house.
    solver.add(name_vars[4] == names.index("Peter"))

    # 2. The tea drinker is the person who loves basketball.
    solver.add(And(drink_vars[i] == drinks.index("tea"), sport_vars[i] == sports.index("basketball")) for i in houses)

    # 3. Arnold is the person who smokes Blue Master.
    solver.add(And(name_vars[i] == names.index("Arnold"), cigar_vars[i] == cigars.index("blue master")) for i in houses)

    # 4. The person who loves basketball is Eric.
    solver.add(And(sport_vars[i] == sports.index("basketball"), name_vars[i] == names.index("Eric")) for i in houses)

    # 5. The person who loves tennis is the person who smokes Blue Master.
    solver.add(And(sport_vars[i] == sports.index("tennis"), cigar_vars[i] == cigars.index("blue master")) for i in houses)

    # 6. There are two houses between the one who only drinks water and Peter.
    solver.add(Abs(drink_vars[i] - drinks.index("water")) == Abs(name_vars[j] - names.index("Peter")) - 2 for i in houses for j in houses if i != j)

    # 7. The coffee drinker is Arnold.
    solver.add(And(drink_vars[i] == drinks.index("coffee"), name_vars[i] == names.index("Arnold")) for i in houses)

    # 8. The person who loves basketball is in the third house.
    solver.add(sport_vars[3] == sports.index("basketball"))

    # 9. The Prince smoker is the person who loves soccer.
    solver.add(And(cigar_vars[i] == cigars.index("prince"), sport_vars[i] == sports.index("soccer")) for i in houses)

    # 10. Peter is the person partial to Pall Mall.
    solver.add(And(name_vars[i] == names.index("Peter"), cigar_vars[i] == cigars.index("pall mall")) for i in houses)

    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
                "rows": []
            }
        }
        for house in houses:
            name = names[model.evaluate(name_vars[house]).as_long()]
            cigar = cigars[model.evaluate(cigar_vars[house]).as_long()]
            sport = sports[model.evaluate(sport_vars[house]).as_long()]
            drink = drinks[model.evaluate(drink_vars[house]).as_long()]
            solution["solution"]["rows"].append([str(house), name, cigar, sport, drink])
        return solution
    else:
        return None

# Solve the puzzle and print the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))