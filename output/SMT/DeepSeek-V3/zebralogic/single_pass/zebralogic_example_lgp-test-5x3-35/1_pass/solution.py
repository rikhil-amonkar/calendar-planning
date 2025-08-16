from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4, 5]

    # Define the variables for each attribute in each house
    names = {h: Const(f'name_{h}', StringSort()) for h in houses}
    mothers = {h: Const(f'mother_{h}', StringSort()) for h in houses}
    heights = {h: Const(f'height_{h}', StringSort()) for h in houses}

    # All possible values for each attribute
    possible_names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
    possible_mothers = ["Kailyn", "Janelle", "Aniya", "Penny", "Holly"]
    possible_heights = ["average", "very short", "short", "very tall", "tall"]

    # Add constraints that each attribute in each house must be one of the possible values
    for h in houses:
        s.add(Or([names[h] == StringVal(n) for n in possible_names]))
        s.add(Or([mothers[h] == StringVal(m) for m in possible_mothers]))
        s.add(Or([heights[h] == StringVal(ht) for ht in possible_heights]))

    # Add uniqueness constraints for names, mothers, and heights across houses
    for h1 in houses:
        for h2 in houses:
            if h1 < h2:
                s.add(names[h1] != names[h2])
                s.add(mothers[h1] != mothers[h2])
                s.add(heights[h1] != heights[h2])

    # Add constraints based on the clues
    # Clue 1: Alice is the person whose mother's name is Aniya.
    for h in houses:
        s.add(Implies(names[h] == StringVal("Alice"), mothers[h] == StringVal("Aniya")))

    # Clue 2: The person who has an average height is somewhere to the left of the person whose mother's name is Penny.
    average_height_house = Int('average_height_house')
    penny_mother_house = Int('penny_mother_house')
    s.add(And(average_height_house >= 1, average_height_house <= 5))
    s.add(And(penny_mother_house >= 1, penny_mother_house <= 5))
    s.add(average_height_house < penny_mother_house)
    for h in houses:
        s.add(Implies(heights[h] == StringVal("average"), average_height_house == h))
        s.add(Implies(mothers[h] == StringVal("Penny"), penny_mother_house == h))

    # Clue 3: The person whose mother's name is Janelle is Bob.
    for h in houses:
        s.add(Implies(mothers[h] == StringVal("Janelle"), names[h] == StringVal("Bob")))

    # Clue 4: Peter is not in the second house.
    s.add(names[2] != StringVal("Peter"))

    # Clue 5: The person who is short is directly left of Arnold.
    short_house = Int('short_house')
    s.add(And(short_house >= 1, short_house <= 4))  # Since Arnold must be to the right
    s.add(heights[short_house] == StringVal("short"))
    s.add(names[short_house + 1] == StringVal("Arnold"))

    # Clue 6: The person who is very tall is Arnold.
    for h in houses:
        s.add(Implies(names[h] == StringVal("Arnold"), heights[h] == StringVal("very tall")))

    # Clue 7: Bob is directly left of the person who has an average height.
    bob_house = Int('bob_house')
    s.add(And(bob_house >= 1, bob_house <= 4))  # Since average height is to the right
    s.add(names[bob_house] == StringVal("Bob"))
    s.add(heights[bob_house + 1] == StringVal("average"))

    # Clue 8: Eric is not in the fifth house.
    s.add(names[5] != StringVal("Eric"))

    # Clue 9: The person who is very tall is somewhere to the right of the person whose mother's name is Holly.
    holly_mother_house = Int('holly_mother_house')
    very_tall_house = Int('very_tall_house')
    s.add(And(holly_mother_house >= 1, holly_mother_house <= 5))
    s.add(And(very_tall_house >= 1, very_tall_house <= 5))
    s.add(holly_mother_house < very_tall_house)
    for h in houses:
        s.add(Implies(mothers[h] == StringVal("Holly"), holly_mother_house == h))
        s.add(Implies(heights[h] == StringVal("very tall"), very_tall_house == h))

    # Clue 10: Eric is the person whose mother's name is Kailyn.
    for h in houses:
        s.add(Implies(names[h] == StringVal("Eric"), mothers[h] == StringVal("Kailyn")))

    # Clue 11: The person who is very short is in the fifth house.
    s.add(heights[5] == StringVal("very short"))

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Mother", "Height"],
                "rows": []
            }
        }
        for h in sorted(houses):
            name_val = model.evaluate(names[h])
            mother_val = model.evaluate(mothers[h])
            height_val = model.evaluate(heights[h])
            solution["solution"]["rows"].append([
                str(h),
                str(name_val),
                str(mother_val),
                str(height_val)
            ])
        return solution
    else:
        return {"solution": {"header": ["House", "Name", "Mother", "Height"], "rows": []}}

# Run the solver and print the result
solution = solve_scheduling_problem()
import json
print(json.dumps(solution, indent=2))