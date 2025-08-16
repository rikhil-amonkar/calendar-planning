from z3 import *

def solve_scheduling_problem():
    # Define EnumSorts
    Names, (Eric, Arnold) = EnumSort('Names', ['Eric', 'Arnold'])
    Hobbies, (Photography, Gardening) = EnumSort('Hobbies', ['photography', 'gardening'])
    Pets, (Cat, Dog) = EnumSort('Pets', ['cat', 'dog'])
    Heights, (Short, VeryShort) = EnumSort('Heights', ['short', 'very_short'])

    # Variables for each house
    name1 = Const('name1', Names)
    name2 = Const('name2', Names)
    hobby1 = Const('hobby1', Hobbies)
    hobby2 = Const('hobby2', Hobbies)
    pet1 = Const('pet1', Pets)
    pet2 = Const('pet2', Pets)
    height1 = Const('height1', Heights)
    height2 = Const('height2', Heights)

    solver = Solver()

    # Uniqueness constraints
    solver.add(Distinct(name1, name2))
    solver.add(Distinct(hobby1, hobby2))
    solver.add(Distinct(pet1, pet2))
    solver.add(Distinct(height1, height2))

    # Clue 1: very short → photography
    solver.add(Implies(height1 == VeryShort, hobby1 == Photography))
    solver.add(Implies(height2 == VeryShort, hobby2 == Photography))

    # Clue 2: Eric → very short
    solver.add(Implies(name1 == Eric, height1 == VeryShort))
    solver.add(Implies(name2 == Eric, height2 == VeryShort))

    # Clue 3: cat is to the right of very short
    solver.add(Implies(height2 == VeryShort, False))  # very_short must be in house 1
    solver.add(Implies(height1 == VeryShort, pet2 == Cat))

    if solver.check() == sat:
        model = solver.model()
        # Prepare the solution rows
        rows = []
        for i, (n, h, p, he) in enumerate([(name1, hobby1, pet1, height1), (name2, hobby2, pet2, height2)]):
            house_num = i + 1
            name_val = model[n].decl().name()
            hobby_val = model[h].decl().name()
            pet_val = model[p].decl().name()
            height_val = model[he].decl().name()
            rows.append([str(house_num), name_val, hobby_val, pet_val, height_val])
        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Pet", "Height"],
                "rows": rows
            }
        }
        return solution
    else:
        return {"solution": None}

# Call the function and print the JSON
solution = solve_scheduling_problem()
import json
print(json.dumps(solution, indent=2))