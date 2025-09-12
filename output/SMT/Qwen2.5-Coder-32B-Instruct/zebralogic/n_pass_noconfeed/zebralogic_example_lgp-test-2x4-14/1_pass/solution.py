from z3 import *

def solve_puzzle():
    # Define variables
    names = ['Eric', 'Arnold']
    house_styles = ['victorian', 'colonial']
    smoothies = ['cherry', 'desert']
    pets = ['dog', 'cat']
    houses = [1, 2]

    # Create Solver instance
    solver = Solver()

    # Declare variables for each attribute in each house
    name_vars = [[String(f'name_{h}_{n}') for n in names] for h in houses]
    house_style_vars = [[String(f'house_style_{h}_{s}') for s in house_styles] for h in houses]
    smoothie_vars = [[String(f'smoothie_{h}_{sm}') for sm in smoothies] for h in houses]
    pet_vars = [[String(f'pet_{h}_{p}') for p in pets] for h in houses]

    # Add constraints for each house
    for h in houses:
        solver.add(Or([name_vars[h-1][names.index(n)] == str(h) for n in names]))
        solver.add(Or([house_style_vars[h-1][house_styles.index(s)] == str(h) for s in house_styles]))
        solver.add(Or([smoothie_vars[h-1][smoothies.index(sm)] == str(h) for sm in smoothies]))
        solver.add(Or([pet_vars[h-1][pets.index(p)] == str(h) for p in pets]))

        # Ensure each attribute is unique per house
        solver.add(Distinct([name_vars[h-1][names.index(n)] for n in names]))
        solver.add(Distinct([house_style_vars[h-1][house_styles.index(s)] for s in house_styles]))
        solver.add(Distinct([smoothie_vars[h-1][smoothies.index(sm)] for sm in smoothies]))
        solver.add(Distinct([pet_vars[h-1][pets.index(p)] for p in pets]))

    # Add constraints between houses
    solver.add(Distinct([name_vars[0][names.index(n)] for n in names]))
    solver.add(Distinct([house_style_vars[0][house_styles.index(s)] for s in house_styles]))
    solver.add(Distinct([smoothie_vars[0][smoothies.index(sm)] for sm in smoothies]))
    solver.add(Distinct([pet_vars[0][pets.index(p)] for p in pets]))

    solver.add(Distinct([name_vars[1][names.index(n)] for n in names]))
    solver.add(Distinct([house_style_vars[1][house_styles.index(s)] for s in house_styles]))
    solver.add(Distinct([smoothie_vars[1][smoothies.index(sm)] for sm in smoothies]))
    solver.add(Distinct([pet_vars[1][pets.index(p)] for p in pets]))

    # Clue 1: The person who likes Cherry smoothies is the person who owns a dog.
    solver.add(Implies(smoothie_vars[0][smoothies.index('cherry')] == '1', pet_vars[0][pets.index('dog')] == '1'))
    solver.add(Implies(smoothie_vars[0][smoothies.index('cherry')] == '2', pet_vars[0][pets.index('dog')] == '2'))
    solver.add(Implies(smoothie_vars[1][smoothies.index('cherry')] == '1', pet_vars[1][pets.index('dog')] == '1'))
    solver.add(Implies(smoothie_vars[1][smoothies.index('cherry')] == '2', pet_vars[1][pets.index('dog')] == '2'))

    # Clue 2: The person residing in a Victorian house is the person who owns a dog.
    solver.add(Implies(house_style_vars[0][house_styles.index('victorian')] == '1', pet_vars[0][pets.index('dog')] == '1'))
    solver.add(Implies(house_style_vars[0][house_styles.index('victorian')] == '2', pet_vars[0][pets.index('dog')] == '2'))
    solver.add(Implies(house_style_vars[1][house_styles.index('victorian')] == '1', pet_vars[1][pets.index('dog')] == '1'))
    solver.add(Implies(house_style_vars[1][house_styles.index('victorian')] == '2', pet_vars[1][pets.index('dog')] == '2'))

    # Clue 3: The person residing in a Victorian house is somewhere to the left of Eric.
    solver.add(Implies(house_style_vars[0][house_styles.index('victorian')] == '1', name_vars[0][names.index('Eric')] != '1'))
    solver.add(Implies(house_style_vars[0][house_styles.index('victorian')] == '2', name_vars[1][names.index('Eric')] != '1'))

    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
                "rows": []
            }
        }

        for h in houses:
            house_data = [str(h)]
            for n in names:
                if model.evaluate(name_vars[h-1][names.index(n)]) == str(h):
                    house_data.append(n)
            for s in house_styles:
                if model.evaluate(house_style_vars[h-1][house_styles.index(s)]) == str(h):
                    house_data.append(s)
            for sm in smoothies:
                if model.evaluate(smoothie_vars[h-1][smoothies.index(sm)]) == str(h):
                    house_data.append(sm)
            for p in pets:
                if model.evaluate(pet_vars[h-1][pets.index(p)]) == str(h):
                    house_data.append(p)
            solution["solution"]["rows"].append(house_data)

        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

solve_puzzle()