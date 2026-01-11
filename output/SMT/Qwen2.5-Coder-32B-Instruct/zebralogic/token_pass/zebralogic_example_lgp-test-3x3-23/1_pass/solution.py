from z3 import *

# Define the variables for each house
names = ['Peter', 'Arnold', 'Eric']
occupations = ['doctor', 'teacher', 'engineer']
hobbies = ['cooking', 'photography', 'gardening']

# Create symbolic variables for each house
house1_name = Int('house1_name')
house2_name = Int('house2_name')
house3_name = Int('house3_name')

house1_occupation = Int('house1_occupation')
house2_occupation = Int('house2_occupation')
house3_occupation = Int('house3_occupation')

house1_hobby = Int('house1_hobby')
house2_hobby = Int('house2_hobby')
house3_hobby = Int('house3_hobby')

# Map symbolic variables to their respective domains
s = Solver()

# Each variable represents an index into the lists names, occupations, hobbies
s.add(Or(house1_name == 0, house1_name == 1, house1_name == 2))
s.add(Or(house2_name == 0, house2_name == 1, house2_name == 2))
s.add(Or(house3_name == 0, house3_name == 1, house3_name == 2))

s.add(Or(house1_occupation == 0, house1_occupation == 1, house1_occupation == 2))
s.add(Or(house2_occupation == 0, house2_occupation == 1, house2_occupation == 2))
s.add(Or(house3_occupation == 0, house3_occupation == 1, house3_occupation == 2))

s.add(Or(house1_hobby == 0, house1_hobby == 1, house1_hobby == 2))
s.add(Or(house2_hobby == 0, house2_hobby == 1, house2_hobby == 2))
s.add(Or(house3_hobby == 0, house3_hobby == 1, house3_hobby == 2))

# Uniqueness constraints
s.add(Distinct(house1_name, house2_name, house3_name))
s.add(Distinct(house1_occupation, house2_occupation, house3_occupation))
s.add(Distinct(house1_hobby, house2_hobby, house3_hobby))

# Clue 1: The person who is a doctor and Eric are next to each other.
s.add(Implies(house1_name == 2, house2_occupation == 0))  # Eric in house 1, doctor in house 2
s.add(Implies(house2_name == 2, Or(house1_occupation == 0, house3_occupation == 0)))  # Eric in house 2, doctor in house 1 or 3
s.add(Implies(house3_name == 2, house2_occupation == 0))  # Eric in house 3, doctor in house 2

# Clue 2: The person who loves cooking is directly left of the person who is a teacher.
s.add(Implies(house1_hobby == 0, house2_occupation == 1))  # Cooking in house 1, teacher in house 2
s.add(Implies(house2_hobby == 0, house3_occupation == 1))  # Cooking in house 2, teacher in house 3

# Clue 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening.
s.add(Implies(house1_hobby == 2, Or(house2_occupation == 0, house3_occupation == 0)))  # Gardening in house 1, doctor in house 2 or 3
s.add(Implies(house2_hobby == 2, house3_occupation == 0))  # Gardening in house 2, doctor in house 3

# Clue 4: The photography enthusiast is the person who is a teacher.
s.add(house1_hobby == 1 == house1_occupation)
s.add(house2_hobby == 1 == house2_occupation)
s.add(house3_hobby == 1 == house3_occupation)

# Clue 5: The person who is an engineer is Peter.
s.add(Implies(house1_occupation == 2, house1_name == 0))  # Engineer in house 1, Peter in house 1
s.add(Implies(house2_occupation == 2, house2_name == 0))  # Engineer in house 2, Peter in house 2
s.add(Implies(house3_occupation == 2, house3_name == 0))  # Engineer in house 3, Peter in house 3

# Solve the problem
if s.check() == sat:
    m = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Hobby"],
            "rows": [
                ["1", names[m[house1_name].as_long()], occupations[m[house1_occupation].as_long()], hobbies[m[house1_hobby].as_long()]],
                ["2", names[m[house2_name].as_long()], occupations[m[house2_occupation].as_long()], hobbies[m[house2_hobby].as_long()]],
                ["3", names[m[house3_name].as_long()], occupations[m[house3_occupation].as_long()], hobbies[m[house3_hobby].as_long()]]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")