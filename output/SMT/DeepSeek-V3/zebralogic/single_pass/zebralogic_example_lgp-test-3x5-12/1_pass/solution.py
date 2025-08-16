from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    s = Solver()

    # Define the houses
    houses = [1, 2, 3]

    # Define the attributes
    names = ["Eric", "Peter", "Arnold"]
    cigars = ["blue master", "prince", "pall mall"]
    hobbies = ["photography", "gardening", "cooking"]
    educations = ["high school", "associate", "bachelor"]
    drinks = ["tea", "milk", "water"]

    # Create variables for each attribute in each house
    name = {h: String(f"name_{h}") for h in houses}
    cigar = {h: String(f"cigar_{h}") for h in houses}
    hobby = {h: String(f"hobby_{h}") for h in houses}
    education = {h: String(f"education_{h}") for h in houses}
    drink = {h: String(f"drink_{h}") for h in houses}

    # Add constraints that each attribute is one of the possible values
    for h in houses:
        s.add(Or([name[h] == n for n in names]))
        s.add(Or([cigar[h] == c for c in cigars]))
        s.add(Or([hobby[h] == ho for ho in hobbies]))
        s.add(Or([education[h] == e for e in educations]))
        s.add(Or([drink[h] == d for d in drinks]))

    # Add uniqueness constraints for each attribute across houses
    for attr in [name, cigar, hobby, education, drink]:
        for h1 in houses:
            for h2 in houses:
                if h1 < h2:
                    s.add(attr[h1] != attr[h2])

    # Clue 1: The person partial to Pall Mall is Peter.
    for h in houses:
        s.add(Implies(cigar[h] == "pall mall", name[h] == "Peter"))

    # Clue 2: The person who likes milk is directly left of the person with a high school diploma.
    s.add(Or(
        And(drink[1] == "milk", education[2] == "high school"),
        And(drink[2] == "milk", education[3] == "high school")
    ))

    # Clue 3: Eric is the tea drinker.
    for h in houses:
        s.add(Implies(name[h] == "Eric", drink[h] == "tea"))

    # Clue 4: Arnold and the Prince smoker are next to each other.
    for h1 in houses:
        for h2 in houses:
            if abs(h1 - h2) == 1:
                s.add(Or(
                    And(name[h1] == "Arnold", cigar[h2] == "prince"),
                    And(name[h2] == "Arnold", cigar[h1] == "prince")
                ))

    # Clue 5: The person who enjoys gardening is somewhere to the left of the Prince smoker.
    for h_prince in houses:
        for h_gardening in houses:
            if h_gardening < h_prince:
                s.add(Implies(cigar[h_prince] == "prince", hobby[h_gardening] == "gardening"))

    # Clue 6: The person who likes milk is the person with an associate's degree.
    for h in houses:
        s.add(Implies(drink[h] == "milk", education[h] == "associate"))

    # Clue 7: The person with a bachelor's degree is directly left of the photography enthusiast.
    s.add(Or(
        And(education[1] == "bachelor", hobby[2] == "photography"),
        And(education[2] == "bachelor", hobby[3] == "photography")
    ))

    # Check if the problem is solvable
    if s.check() == sat:
        model = s.model()
        # Prepare the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
                "rows": []
            }
        }
        for h in sorted(houses):
            row = [
                str(h),
                str(model.eval(name[h])),
                str(model.eval(cigar[h])),
                str(model.eval(hobby[h])),
                str(model.eval(education[h])),
                str(model.eval(drink[h]))
            ]
            solution["solution"]["rows"].append(row)
        return solution
    else:
        return {"solution": {"header": [], "rows": []}}

# Solve the problem and print the result
import json
print(json.dumps(solve_scheduling_problem(), indent=2))