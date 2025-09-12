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
    def find_house(condition, model):
        return next(house for house in houses if model.evaluate(condition(house)))

    # Add specific constraints
    arnold_index = names.index("Arnold")
    solver.add(name_vars[5] == arnold_index)  # Assuming Arnold is in the 5th house based on the problem statement
    lawyer_index = occupations.index("lawyer")
    cruise_index = vacations.index("cruise")
    solver.add(occupation_vars[cruise_index + 1] == lawyer_index)  # Adding 1 because houses are 1-indexed
    bob_index = names.index("Bob")
    doctorate_index = educations.index("doctorate")
    solver.add(name_vars[doctorate_index + 1] == bob_index)  # Adding 1 because houses are 1-indexed
    associate_index = educations.index("associate")
    solver.add(education_vars[cruise_index + 1] == associate_index)  # Adding 1 because houses are 1-indexed
    peter_index = names.index("Peter")
    solver.add(name_vars[1] != peter_index)
    artist_index = occupations.index("artist")
    solver.add(name_vars[artist_index + 1] == peter_index)  # Adding 1 because houses are 1-indexed
    master_index = educations.index("master")
    camping_index = vacations.index("camping")
    solver.add(education_vars[camping_index + 1] == master_index)  # Adding 1 because houses are 1-indexed
    dane_index = nationalities.index("dane")
    doctor_index = occupations.index("doctor")
    solver.add(occupation_vars[dane_index + 1] - 1 == occupation_vars[doctor_index + 1])  # Adding 1 because houses are 1-indexed
    associate_index = educations.index("associate")
    engineer_index = occupations.index("engineer")
    solver.add(occupation_vars[associate_index + 1] - 1 == occupation_vars[engineer_index + 1])  # Adding 1 because houses are 1-indexed
    brit_index = nationalities.index("brit")
    solver.add(nationality_vars[camping_index + 1] == brit_index)  # Adding 1 because houses are 1-indexed
    norwegian_index = nationalities.index("norwegian")
    bachelor_index = educations.index("bachelor")
    solver.add(Or(
        And(nationality_vars[1] == norwegian_index, education_vars[2] == bachelor_index),
        And(nationality_vars[2] == norwegian_index, education_vars[1] == bachelor_index),
        And(nationality_vars[2] == norwegian_index, education_vars[3] == bachelor_index),
        And(nationality_vars[3] == norwegian_index, education_vars[2] == bachelor_index),
        And(nationality_vars[3] == norwegian_index, education_vars[4] == bachelor_index),
        And(nationality_vars[4] == norwegian_index, education_vars[3] == bachelor_index),
        And(nationality_vars[4] == norwegian_index, education_vars[5] == bachelor_index),
        And(nationality_vars[5] == norwegian_index, education_vars[4] == bachelor_index)
    ))
    eric_index = names.index("Eric")
    solver.add(name_vars[camping_index + 1] == eric_index)  # Adding 1 because houses are 1-indexed
    german_index = nationalities.index("german")
    teacher_index = occupations.index("teacher")
    solver.add(nationality_vars[teacher_index + 1] == german_index)  # Adding 1 because houses are 1-indexed
    beach_index = vacations.index("beach")
    city_index = vacations.index("city")
    solver.add(vacation_vars[beach_index + 1] < vacation_vars[city_index + 1])  # Adding 1 because houses are 1-indexed
    mountain_index = vacations.index("mountain")
    solver.add(vacation_vars[5] == mountain_index)
    solver.add(vacation_vars[cruise_index + 1] > vacation_vars[beach_index + 1])  # Adding 1 because houses are 1-indexed
    solver.add(education_vars[3] == bachelor_index)

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