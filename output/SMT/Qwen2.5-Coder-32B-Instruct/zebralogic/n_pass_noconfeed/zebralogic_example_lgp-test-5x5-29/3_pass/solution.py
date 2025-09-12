from z3 import *

def solve_puzzle():
    # Define the domain
    houses = [1, 2, 3, 4, 5]
    names = ["Eric", "Peter", "Alice", "Bob", "Arnold"]
    nationalities = ["norwegian", "brit", "swede", "dane", "german"]
    vacations = ["cruise", "mountain", "camping", "beach", "city"]
    educations = ["bachelor", "master", "associate", "doctorate", "high school"]
    occupations = ["artist", "doctor", "engineer", "teacher", "lawyer"]

    # Create a solver instance
    solver = Solver()

    # Declare variables
    name_vars = {house: Int(f"name_{house}") for house in houses}
    nationality_vars = {house: Int(f"nationality_{house}") for house in houses}
    vacation_vars = {house: Int(f"vacation_{house}") for house in houses}
    education_vars = {house: Int(f"education_{house}") for house in houses}
    occupation_vars = {house: Int(f"occupation_{house}") for house in houses}

    # Add constraints for unique values in each category
    for var_dict, domain in [(name_vars, names), (nationality_vars, nationalities),
                             (vacation_vars, vacations), (education_vars, educations),
                             (occupation_vars, occupations)]:
        for house in houses:
            solver.add(var_dict[house] >= 0)
            solver.add(var_dict[house] < len(domain))
        solver.add(Distinct([var_dict[house] for house in houses]))

    # Helper function to find the house given a condition
    def find_house(condition):
        return next(house for house in houses if solver.model().evaluate(condition(house)))

    # Add specific constraints
    solver.add(find_house(lambda house: occupation_vars[house] == occupations.index("lawyer")) == houses[vacations.index("cruise")])
    solver.add(name_vars[houses.index("Arnold")] == names.index("Arnold"))
    solver.add(find_house(lambda house: name_vars[house] == names.index("Bob")) == houses[educations.index("doctorate")])
    solver.add(find_house(lambda house: vacation_vars[house] == vacations.index("cruise")) == houses[educations.index("associate")])
    solver.add(name_vars[1] != names.index("Peter"))
    solver.add(find_house(lambda house: name_vars[house] == names.index("Peter")) == houses[occupations.index("artist")])
    solver.add(find_house(lambda house: vacation_vars[house] == vacations.index("camping")) == houses[educations.index("master")])
    solver.add(find_house(lambda house: occupation_vars[house] == occupations.index("doctor")) + 1 == houses[nationalities.index("dane")])
    solver.add(find_house(lambda house: education_vars[house] == educations.index("associate")) + 1 == houses[occupations.index("engineer")])
    solver.add(find_house(lambda house: vacation_vars[house] == vacations.index("camping")) == houses[nationalities.index("brit")])
    solver.add(Or(
        And(nationality_vars[1] == nationalities.index("norwegian"), education_vars[2] == educations.index("bachelor")),
        And(nationality_vars[2] == nationalities.index("norwegian"), education_vars[1] == educations.index("bachelor")),
        And(nationality_vars[2] == nationalities.index("norwegian"), education_vars[3] == educations.index("bachelor")),
        And(nationality_vars[3] == nationalities.index("norwegian"), education_vars[2] == educations.index("bachelor")),
        And(nationality_vars[3] == nationalities.index("norwegian"), education_vars[4] == educations.index("bachelor")),
        And(nationality_vars[4] == nationalities.index("norwegian"), education_vars[3] == educations.index("bachelor")),
        And(nationality_vars[4] == nationalities.index("norwegian"), education_vars[5] == educations.index("bachelor")),
        And(nationality_vars[5] == nationalities.index("norwegian"), education_vars[4] == educations.index("bachelor"))
    ))
    solver.add(find_house(lambda house: name_vars[house] == names.index("Eric")) == houses[vacations.index("camping")])
    solver.add(find_house(lambda house: name_vars[house] == names.index("Alice")) == houses[nationalities.index("german")])
    solver.add(vacation_vars[houses[vacations.index("beach")]] < vacation_vars[houses[vacations.index("city")]])
    solver.add(vacation_vars[5] == vacations.index("mountain"))
    solver.add(vacation_vars[houses[vacations.index("cruise")]] > vacation_vars[houses[vacations.index("beach")]])
    solver.add(education_vars[3] == educations.index("bachelor"))

    # Check if the model is satisfiable
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for house in houses:
            name = names[model[name_vars[house]].as_long()]
            nationality = nationalities[model[nationality_vars[house]].as_long()]
            vacation = vacations[model[vacation_vars[house]].as_long()]
            education = educations[model[education_vars[house]].as_long()]
            occupation = occupations[model[occupation_vars[house]].as_long()]
            solution.append([str(house), name, nationality, vacation, education, occupation])
        return {
            "solution": {
                "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                "rows": solution
            }
        }
    else:
        return None

import json
print(json.dumps(solve_puzzle(), indent=2))