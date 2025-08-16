from z3 import *
import json

# Mapping dictionaries: each attribute's possible values.
# We'll represent each value as an integer.
# Names: Arnold=0, Alice=1, Eric=2, Peter=3
NAMES = {0: "Arnold", 1: "Alice", 2: "Eric", 3: "Peter"}
# Hobbies: cooking=0, painting=1, photography=2, gardening=3
HOBBIES = {0: "cooking", 1: "painting", 2: "photography", 3: "gardening"}
# Birthdays: april=0, jan=1, sept=2, feb=3
BIRTHDAYS = {0: "april", 1: "jan", 2: "sept", 3: "feb"}
# Educations: master=0, bachelor=1, associate=2, high school=3
EDUCATIONS = {0: "master", 1: "bachelor", 2: "associate", 3: "high school"}
# Smoothies: cherry=0, watermelon=1, desert=2, dragonfruit=3
SMOOTHIES = {0: "cherry", 1: "watermelon", 2: "desert", 3: "dragonfruit"}

# Create the Z3 solver instance
s = Solver()
num_houses = 4  # Houses 1 through 4

# For each house, we create integer variables for each attribute.
names = [Int(f"name_{i}") for i in range(num_houses)]
hobbies = [Int(f"hobby_{i}") for i in range(num_houses)]
birthdays = [Int(f"birthday_{i}") for i in range(num_houses)]
educations = [Int(f"education_{i}") for i in range(num_houses)]
smoothies = [Int(f"smoothie_{i}") for i in range(num_houses)]

# Each variable must be one of 0,1,2,3.
for i in range(num_houses):
    s.add(And(names[i] >= 0, names[i] < 4))
    s.add(And(hobbies[i] >= 0, hobbies[i] < 4))
    s.add(And(birthdays[i] >= 0, birthdays[i] < 4))
    s.add(And(educations[i] >= 0, educations[i] < 4))
    s.add(And(smoothies[i] >= 0, smoothies[i] < 4))

# All houses have different values for each attribute.
s.add(Distinct(names))
s.add(Distinct(hobbies))
s.add(Distinct(birthdays))
s.add(Distinct(educations))
s.add(Distinct(smoothies))

# -----------------------------
# Encode the clues:
# -----------------------------

# Clue 4: The person with a high school diploma is in the third house.
# (House numbering: index0=House1, index1=House2, index2=House3, index3=House4)
s.add(educations[2] == 3)  # high school maps to 3

# Clue 9: The person with a high school diploma is also the person whose birthday is in September.
s.add(birthdays[2] == 2)   # sept maps to 2

# Clue 8: There is one house between the Dragonfruit smoothie lover and the person whose birthday is in September.
# Since the only house with sept is house3 (index2), the dragonfruit smoothie (dragonfruit=3) must be two houses away.
# The only possibility is house1 (index0), because |0-2| = 2.
s.add(smoothies[0] == 3)

# Clue 5: The Watermelon smoothie lover is not in the third house.
s.add(smoothies[2] != 1)  # watermelon maps to 1

# For each house apply the following constraints:
for i in range(num_houses):
    # Clue 1: The Desert smoothie lover is the person whose birthday is in January.
    # desert = 2 and jan = 1.
    s.add(Implies(smoothies[i] == 2, birthdays[i] == 1))
    
    # Clue 3: The person whose birthday is in January is the person with a bachelor's degree.
    # jan = 1 and bachelor = 1.
    s.add(Implies(birthdays[i] == 1, educations[i] == 1))
    
    # Clue 2: Eric is the person with a bachelor's degree.
    # Eric = 2.
    s.add(Implies(names[i] == 2, educations[i] == 1))
    
    # Clue 6: The person with an associate's degree is Arnold.
    # Arnold = 0 and associate = 2.
    s.add(Implies(names[i] == 0, educations[i] == 2))
    
    # Clue 7: The person with a master's degree is the person who paints.
    # master = 0 and painting = 1.
    # We enforce the bi-implication: if education is master then hobby is painting, otherwise hobby is not painting.
    s.add(If(educations[i] == 0, hobbies[i] == 1, hobbies[i] != 1))
    
    # Clue 12: The person who paints as a hobby is the person whose birthday is in February.
    # painting = 1 and feb = 3.
    s.add(If(hobbies[i] == 1, birthdays[i] == 3, birthdays[i] != 3))
    
    # Clue 10: The person who loves cooking is Alice.
    # cooking = 0 and Alice = 1.
    s.add(If(names[i] == 1, hobbies[i] == 0, hobbies[i] != 0))

# Clue 11: The person whose birthday is in April and the person who enjoys gardening are next to each other.
# april = 0 and gardening = 3.
adjacent_pairs = []
for i in range(num_houses - 1):
    adjacent_pairs.append(And(birthdays[i] == 0, hobbies[i+1] == 3))
    adjacent_pairs.append(And(birthdays[i+1] == 0, hobbies[i] == 3))
s.add(Or(adjacent_pairs))

# -----------------------------
# Solve and extract the model:
# -----------------------------
if s.check() == sat:
    m = s.model()
    solution_rows = []
    for i in range(num_houses):
        # Convert the house index (0-based) to its number (1-based)
        house_num = str(i + 1)
        name_val = NAMES[m[names[i]].as_long()]
        hobby_val = HOBBIES[m[hobbies[i]].as_long()]
        birthday_val = BIRTHDAYS[m[birthdays[i]].as_long()]
        education_val = EDUCATIONS[m[educations[i]].as_long()]
        smoothie_val = SMOOTHIES[m[smoothies[i]].as_long()]
        solution_rows.append([house_num, name_val, hobby_val, birthday_val, education_val, smoothie_val])
    
    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
            "rows": solution_rows
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found")