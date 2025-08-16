from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3]

# Define the attributes
names = ["Peter", "Arnold", "Eric"]
occupations = ["doctor", "teacher", "engineer"]
hobbies = ["cooking", "photography", "gardening"]

# Create variables for each attribute in each house
name = {h: String(f"name_{h}") for h in houses}
occupation = {h: String(f"occupation_{h}") for h in houses}
hobby = {h: String(f"hobby_{h}") for h in houses}

# Add constraints that each attribute is one of the possible values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([occupation[h] == o for o in occupations]))
    s.add(Or([hobby[h] == hb for hb in hobbies]))

# Add constraints that all attributes in each category are distinct
s.add(Distinct([name[h] for h in houses]))
s.add(Distinct([occupation[h] for h in houses]))
s.add(Distinct([hobby[h] for h in houses]))

# Clue 1: The person who is a doctor and Eric are next to each other.
for h in houses:
    for neighbor in [h-1, h+1]:
        if neighbor in houses:
            s.add(Implies(occupation[h] == "doctor", name[neighbor] == "Eric"))
            s.add(Implies(name[h] == "Eric", occupation[neighbor] == "doctor"))

# Clue 2: The person who loves cooking is directly left of the person who is a teacher.
for h in [1, 2]:
    s.add(Implies(hobby[h] == "cooking", occupation[h+1] == "teacher"))

# Clue 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening.
for h in houses:
    for left in range(1, h):
        s.add(Implies(occupation[h] == "doctor", hobby[left] == "gardening"))

# Clue 4: The photography enthusiast is the person who is a teacher.
for h in houses:
    s.add(Implies(occupation[h] == "teacher", hobby[h] == "photography"))

# Clue 5: The person who is an engineer is Peter.
for h in houses:
    s.add(Implies(occupation[h] == "engineer", name[h] == "Peter"))

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Hobby"],
            "rows": []
        }
    }
    for h in sorted(houses):
        row = [
            str(h),
            str(model.eval(name[h])),
            str(model.eval(occupation[h])),
            str(model.eval(hobby[h]))
        ]
        solution["solution"]["rows"].append(row)
    print(solution)
else:
    print("No solution found")