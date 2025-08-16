from z3 import *
import json

# Create Z3 solver
s = Solver()

# Define integer variables for each attribute in each category.
# They represent the house number (1 to 3) for the given value.
aArnold   = Int("aArnold")
aPeter    = Int("aPeter")
aEric     = Int("aEric")

dDoctor   = Int("dDoctor")
dTeacher  = Int("dTeacher")
dEngineer = Int("dEngineer")

edAssociate   = Int("edAssociate")
edHighSchool  = Int("edHighSchool")
edBachelor    = Int("edBachelor")

smDesert      = Int("smDesert")
smCherry      = Int("smCherry")
smWatermelon  = Int("smWatermelon")

hGardening    = Int("hGardening")
hCooking      = Int("hCooking")
hPhotography  = Int("hPhotography")

# List of all variables to set domain constraints.
all_vars = [
    aArnold, aPeter, aEric,
    dDoctor, dTeacher, dEngineer,
    edAssociate, edHighSchool, edBachelor,
    smDesert, smCherry, smWatermelon,
    hGardening, hCooking, hPhotography
]

# All variables represent a house number 1 to 3.
for var in all_vars:
    s.add(And(var >= 1, var <= 3))

# Each category: the values must be assigned to distinct houses.
s.add(Distinct(aArnold, aPeter, aEric))
s.add(Distinct(dDoctor, dTeacher, dEngineer))
s.add(Distinct(edAssociate, edHighSchool, edBachelor))
s.add(Distinct(smDesert, smCherry, smWatermelon))
s.add(Distinct(hGardening, hCooking, hPhotography))

# Clue 1: The Desert smoothie lover is the person who is a doctor.
s.add(smDesert == dDoctor)

# Clue 2: Arnold is not in the third house.
s.add(aArnold != 3)

# Clue 3: The person who likes Cherry smoothies is somewhere to the right of Peter.
s.add(smCherry > aPeter)

# Clue 4: The person who loves cooking is in the second house.
s.add(hCooking == 2)

# Clue 5: The person who loves cooking is Peter.
s.add(aPeter == hCooking)

# Clue 6: The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
s.add(edAssociate > hGardening)

# Clue 7: The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
s.add(edBachelor > smDesert)

# Clue 8: The person who loves cooking is the person who is a doctor.
s.add(hCooking == dDoctor)

# Clue 9: The photography enthusiast is the person who is a teacher.
s.add(hPhotography == dTeacher)

# Solve the constraints.
if s.check() == sat:
    m = s.model()
    
    # Prepare a mapping from house number to the final attributes.
    # For each house, we determine the corresponding Name, Occupation, Education, Smoothie, and Hobby.
    houses = {}
    for house in range(1, 4):
        # Determine the Name based on the house number.
        if m[aArnold].as_long() == house:
            name = "Arnold"
        elif m[aPeter].as_long() == house:
            name = "Peter"
        elif m[aEric].as_long() == house:
            name = "Eric"
        
        # Determine the Occupation.
        if m[dDoctor].as_long() == house:
            occupation = "doctor"
        elif m[dTeacher].as_long() == house:
            occupation = "teacher"
        elif m[dEngineer].as_long() == house:
            occupation = "engineer"
        
        # Determine the Education.
        if m[edAssociate].as_long() == house:
            education = "associate"
        elif m[edHighSchool].as_long() == house:
            education = "high school"
        elif m[edBachelor].as_long() == house:
            education = "bachelor"
        
        # Determine the Smoothie.
        if m[smDesert].as_long() == house:
            smoothie = "desert"
        elif m[smCherry].as_long() == house:
            smoothie = "cherry"
        elif m[smWatermelon].as_long() == house:
            smoothie = "watermelon"
        
        # Determine the Hobby.
        if m[hGardening].as_long() == house:
            hobby = "gardening"
        elif m[hCooking].as_long() == house:
            hobby = "cooking"
        elif m[hPhotography].as_long() == house:
            hobby = "photography"
        
        houses[house] = [str(house), name, occupation, education, smoothie, hobby]
    
    # Create the final JSON dictionary.
    solution = {
      "solution": {
        "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
        "rows": [
            houses[1],
            houses[2],
            houses[3]
        ]
      }
    }
    
    # Output the solution as formatted JSON.
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")