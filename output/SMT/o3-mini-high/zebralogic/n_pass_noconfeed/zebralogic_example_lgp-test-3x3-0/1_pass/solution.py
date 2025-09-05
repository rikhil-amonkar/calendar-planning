from z3 import Solver, Int, Distinct, Abs
import json

def main():
    # Create a solver instance
    solver = Solver()

    # Define integer variables for the houses (1, 2, 3) for each attribute.
    # Names
    Peter = Int("Peter")
    Eric = Int("Eric")
    Arnold = Int("Arnold")
    
    # Education degrees
    bachelor = Int("bachelor")
    associate = Int("associate")
    high_school = Int("high_school")  # represents "high school" diploma
    
    # Occupations
    teacher = Int("teacher")
    doctor = Int("doctor")
    engineer = Int("engineer")
    
    # Each variable must be in the domain 1..3 (house numbers)
    vars_all = [Peter, Eric, Arnold, bachelor, associate, high_school, teacher, doctor, engineer]
    for var in vars_all:
        solver.add(var >= 1, var <= 3)
    
    # Each attribute category must be a permutation of houses.
    solver.add(Distinct(Peter, Eric, Arnold))
    solver.add(Distinct(bachelor, associate, high_school))
    solver.add(Distinct(teacher, doctor, engineer))
    
    # Clue 1:
    # "The person who is a teacher is directly left of the person with an associate's degree."
    # Teacher's house + 1 equals the house of the person with the associate's degree.
    solver.add(teacher + 1 == associate)
    
    # Clue 2:
    # "The person with an associate's degree and Eric are next to each other."
    solver.add(Abs(associate - Eric) == 1)
    
    # Clue 3:
    # "Peter is the person with a high school diploma."
    solver.add(Peter == high_school)
    
    # Clue 4:
    # "The person who is a doctor is the person with a bachelor's degree."
    solver.add(doctor == bachelor)
    
    # Check satisfiability.
    if solver.check() == 'sat' or solver.check().r == 1:
        model = solver.model()
    else:
        print(json.dumps({"solution": {"header": ["House", "Name", "Education", "Occupation"], "rows": []}}))
        return

    # Prepare a mapping for each house number to its attributes:
    houses = [1, 2, 3]
    solution_rows = []
    
    def get_name(house):
        if model.evaluate(Peter).as_long() == house:
            return "Peter"
        if model.evaluate(Eric).as_long() == house:
            return "Eric"
        if model.evaluate(Arnold).as_long() == house:
            return "Arnold"
        return ""
    
    def get_education(house):
        if model.evaluate(bachelor).as_long() == house:
            return "bachelor"
        if model.evaluate(associate).as_long() == house:
            return "associate"
        if model.evaluate(high_school).as_long() == house:
            return "high school"
        return ""
    
    def get_occupation(house):
        if model.evaluate(teacher).as_long() == house:
            return "teacher"
        if model.evaluate(doctor).as_long() == house:
            return "doctor"
        if model.evaluate(engineer).as_long() == house:
            return "engineer"
        return ""
    
    for house in houses:
        row = [
            str(house),
            get_name(house),
            get_education(house),
            get_occupation(house)
        ]
        solution_rows.append(row)
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Education", "Occupation"],
            "rows": solution_rows
        }
    }
    
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()