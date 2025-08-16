from z3 import *
import json

# Create Z3 integer variables representing the house number (1,2,3)
# for each person, education level, and occupation
Peter = Int('Peter')    # House of Peter
Eric  = Int('Eric')     # House of Eric
Arnold = Int('Arnold')  # House of Arnold

high_school = Int('high_school')    # House with high school diploma
associate   = Int('associate')        # House with associate's degree
bachelor  = Int('bachelor')           # House with bachelor's degree

teacher = Int('teacher')   # House of the teacher
doctor  = Int('doctor')    # House of the doctor
engineer = Int('engineer') # House of the engineer

# Initialize the solver
s = Solver()

# All variables must be between 1 and 3 because there are 3 houses.
vars_list = [Peter, Eric, Arnold, high_school, associate, bachelor, teacher, doctor, engineer]
for var in vars_list:
    s.add(var >= 1, var <= 3)

# All persons must be in different houses.
s.add(Distinct(Peter, Eric, Arnold))
# All education levels are assigned to different houses.
s.add(Distinct(high_school, associate, bachelor))
# All occupations are assigned to different houses.
s.add(Distinct(teacher, doctor, engineer))

# Clue 3: Peter is the person with a high school diploma.
s.add(Peter == high_school)

# Clue 4: The person who is a doctor is the person with a bachelor's degree.
s.add(doctor == bachelor)

# Clue 1: The person who is a teacher is directly left of the person with an associate's degree.
# (The teacher must be immediately to the left, so teacher's house + 1 equals associate's house.)
s.add(teacher + 1 == associate)

# Clue 2: The person with an associate's degree and Eric are next to each other.
s.add(Or(associate - Eric == 1, Eric - associate == 1))

# Check for a solution
if s.check() == sat:
    m = s.model()
    # Build reverse mappings for each house based on the model:
    houseToName = {
        m.evaluate(Peter).as_long(): "Peter",
        m.evaluate(Eric).as_long(): "Eric",
        m.evaluate(Arnold).as_long(): "Arnold"
    }
    
    houseToEdu = {
        m.evaluate(high_school).as_long(): "high school",
        m.evaluate(associate).as_long(): "associate",
        m.evaluate(bachelor).as_long(): "bachelor"
    }
    
    houseToOcc = {
        m.evaluate(teacher).as_long(): "teacher",
        m.evaluate(doctor).as_long(): "doctor",
        m.evaluate(engineer).as_long(): "engineer"
    }
    
    # Assemble the rows in order of houses 1, 2, and 3.
    rows = []
    for h in range(1, 4):
        rows.append([str(h), houseToName[h], houseToEdu[h], houseToOcc[h]])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Education", "Occupation"],
            "rows": rows
        }
    }
    # Output the JSON solution.
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")