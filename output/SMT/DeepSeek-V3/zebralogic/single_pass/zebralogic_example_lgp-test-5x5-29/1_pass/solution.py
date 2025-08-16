import json
from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define the attributes
names = ["Eric", "Peter", "Alice", "Bob", "Arnold"]
nationalities = ["norwegian", "brit", "swede", "dane", "german"]
vacations = ["cruise", "mountain", "camping", "beach", "city"]
educations = ["bachelor", "master", "associate", "doctorate", "high school"]
occupations = ["artist", "doctor", "engineer", "teacher", "lawyer"]

# Create dictionaries to hold the variables for each attribute
name = {h: Const(f'name_{h}', StringSort()) for h in houses}
nationality = {h: Const(f'nationality_{h}', StringSort()) for h in houses}
vacation = {h: Const(f'vacation_{h}', StringSort()) for h in houses}
education = {h: Const(f'education_{h}', StringSort()) for h in houses}
occupation = {h: Const(f'occupation_{h}', StringSort()) for h in houses}

# Add constraints for uniqueness of each attribute
for attr in [name, nationality, vacation, education, occupation]:
    for h1 in houses:
        for h2 in houses:
            if h1 < h2:
                s.add(attr[h1] != attr[h2])

# Each attribute must be one of the allowed values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([nationality[h] == n for n in nationalities]))
    s.add(Or([vacation[h] == v for v in vacations]))
    s.add(Or([education[h] == e for e in educations]))
    s.add(Or([occupation[h] == o for o in occupations]))

# Apply the clues one by one
# Clue 1: The person who likes going on cruises is the person who is a lawyer.
for h in houses:
    s.add(Implies(vacation[h] == "cruise", occupation[h] == "lawyer"))

# Clue 2: The person who loves beach vacations is directly left of Arnold.
for h in houses:
    if h < 5:
        s.add(Implies(vacation[h] == "beach", name[h+1] == "Arnold"))
    else:
        s.add(vacation[h] != "beach")  # beach cannot be in house 5

# Clue 3: The person with a doctorate is somewhere to the left of Bob.
for h in houses:
    if h < 5:
        s.add(Implies(education[h] == "doctorate", Or([name[h2] == "Bob" for h2 in houses if h2 > h])))
    else:
        s.add(Implies(education[h] == "doctorate", False))  # doctorate cannot be in house 5 if Bob is to the right

# Clue 4: The person with an associate's degree is the person who likes going on cruises.
for h in houses:
    s.add(Implies(education[h] == "associate", vacation[h] == "cruise"))

# Clue 5: Peter is not in the first house.
s.add(name[1] != "Peter")

# Clue 6: The person who is an artist is Peter.
for h in houses:
    s.add(Implies(occupation[h] == "artist", name[h] == "Peter"))

# Clue 7: The person who enjoys camping trips is the person with a master's degree.
for h in houses:
    s.add(Implies(vacation[h] == "camping", education[h] == "master"))

# Clue 8: The Dane is somewhere to the right of the person who is a doctor.
for h in houses:
    if h < 5:
        s.add(Implies(occupation[h] == "doctor", Or([nationality[h2] == "dane" for h2 in houses if h2 > h])))
    else:
        s.add(occupation[h] != "doctor")  # doctor cannot be in house 5 if Dane is to the right

# Clue 9: The person with an associate's degree is directly left of the person who is an engineer.
for h in houses:
    if h < 5:
        s.add(Implies(education[h] == "associate", occupation[h+1] == "engineer"))
    else:
        s.add(education[h] != "associate")  # associate cannot be in house 5

# Clue 10: The person who enjoys camping trips is the British person.
for h in houses:
    s.add(Implies(vacation[h] == "camping", nationality[h] == "brit"))

# Clue 11: The Norwegian and the person with a bachelor's degree are next to each other.
for h in houses:
    if h < 5:
        s.add(Or(
            And(nationality[h] == "norwegian", education[h+1] == "bachelor"),
            And(nationality[h+1] == "norwegian", education[h] == "bachelor")
        ))
    else:
        pass  # handled by h < 5 cases

# Clue 12: The person who is an artist is the Swedish person.
for h in houses:
    s.add(Implies(occupation[h] == "artist", nationality[h] == "swede"))

# Clue 13: Bob is not in the fourth house.
s.add(name[4] != "Bob")

# Clue 14: The person who enjoys camping trips is Eric.
for h in houses:
    s.add(Implies(vacation[h] == "camping", name[h] == "Eric"))

# Clue 15: Alice is the German.
for h in houses:
    s.add(Implies(name[h] == "Alice", nationality[h] == "german"))

# Clue 16: The person who loves beach vacations is somewhere to the left of the person who prefers city breaks.
for h in houses:
    if h < 5:
        s.add(Implies(vacation[h] == "beach", Or([vacation[h2] == "city" for h2 in houses if h2 > h])))
    else:
        s.add(vacation[h] != "beach")  # beach cannot be in house 5

# Clue 17: The person who enjoys mountain retreats is in the fifth house.
s.add(vacation[5] == "mountain")

# Clue 18: The person who likes going on cruises is somewhere to the right of the person who loves beach vacations.
for h in houses:
    if h > 1:
        s.add(Implies(vacation[h] == "cruise", Or([vacation[h2] == "beach" for h2 in houses if h2 < h])))
    else:
        s.add(vacation[h] != "cruise")  # cruise cannot be in house 1

# Clue 19: The person with a bachelor's degree is in the third house.
s.add(education[3] == "bachelor")

# Solve the constraints
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            str(model.eval(name[h])),
            str(model.eval(nationality[h])),
            str(model.eval(vacation[h])),
            str(model.eval(education[h])),
            str(model.eval(occupation[h]))
        ]
        solution["solution"]["rows"].append(row)
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")