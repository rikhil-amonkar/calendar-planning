from z3 import *

def solve_puzzle():
    # Define the variables
    houses = [Int(f'house_{i}') for i in range(1, 6)]
    names = ['Arnold', 'Eric', 'Bob', 'Peter', 'Alice']
    smoothies = ['desert', 'watermelon', 'lime', 'cherry', 'dragonfruit']
    nationalities = ['german', 'swede', 'norwegian', 'dane', 'brit']

    # Create dictionaries to map variables to their respective domains
    name_vars = {name: Int(f'name_{name}') for name in names}
    smoothie_vars = {smoothie: Int(f'smoothie_{smoothie}') for smoothie in smoothies}
    nationality_vars = {nationality: Int(f'nationality_{nationality}') for nationality in nationalities}

    # Create the solver
    solver = Solver()

    # Add constraints for each variable to be in the range 1 to 5
    for var in list(name_vars.values()) + list(smoothie_vars.values()) + list(nationality_vars.values()):
        solver.add(var >= 1, var <= 5)

    # All variables must be distinct
    solver.add(Distinct(list(name_vars.values())))
    solver.add(Distinct(list(smoothie_vars.values())))
    solver.add(Distinct(list(nationality_vars.values())))

    # Clue 1: The Dragonfruit smoothie lover is somewhere to the left of Eric.
    solver.add(smoothie_vars['dragonfruit'] < name_vars['Eric'])

    # Clue 2: The Dragonfruit smoothie lover is in the second house.
    solver.add(smoothie_vars['dragonfruit'] == 2)

    # Clue 3: Peter is not in the first house.
    solver.add(name_vars['Peter'] != 1)

    # Clue 4: The Dane and the British person are next to each other.
    solver.add(Abs(nationality_vars['dane'] - nationality_vars['brit']) == 1)

    # Clue 5: The Desert smoothie lover is not in the fifth house.
    solver.add(smoothie_vars['desert'] != 5)

    # Clue 6: The Swedish person is somewhere to the left of the Dragonfruit smoothie lover.
    solver.add(nationality_vars['swede'] < smoothie_vars['dragonfruit'])

    # Clue 7: There are two houses between the person who drinks Lime smoothies and the Dane.
    solver.add(Abs(smoothie_vars['lime'] - nationality_vars['dane']) == 3)

    # Clue 8: Bob is the Dane.
    solver.add(name_vars['Bob'] == nationality_vars['dane'])

    # Clue 9: Alice is the Norwegian.
    solver.add(name_vars['Alice'] == nationality_vars['norwegian'])

    # Clue 10: Alice is in the third house.
    solver.add(name_vars['Alice'] == 3)

    # Clue 11: The Watermelon smoothie lover is in the third house.
    solver.add(smoothie_vars['watermelon'] == 3)

    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Nationality"],
                "rows": []
            }
        }

        # Extract the solution
        for house in range(1, 6):
            name = None
            smoothie = None
            nationality = None
            for n, var in name_vars.items():
                if model.evaluate(var) == house:
                    name = n
            for s, var in smoothie_vars.items():
                if model.evaluate(var) == house:
                    smoothie = s
            for nat, var in nationality_vars.items():
                if model.evaluate(var) == house:
                    nationality = nat
            solution["solution"]["rows"].append([str(house), name, smoothie, nationality])

        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

solve_puzzle()