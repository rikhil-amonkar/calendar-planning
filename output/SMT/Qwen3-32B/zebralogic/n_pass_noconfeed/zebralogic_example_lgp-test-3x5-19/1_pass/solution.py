import z3
import json

s = z3.Solver()

# Create variables for each house (0,1,2) for each category
names = [z3.Int(f'names_{i}') for i in range(3)]
occupations = [z3.Int(f'occupations_{i}') for i in range(3)]
education = [z3.Int(f'education_{i}') for i in range(3)]
smoothie = [z3.Int(f'smoothie_{i}') for i in range(3)]
hobbies = [z3.Int(f'hobbies_{i}') for i in range(3)]

# Add distinct and range constraints
s.add(z3.Distinct(names))
s.add(z3.Distinct(occupations))
s.add(z3.Distinct(education))
s.add(z3.Distinct(smoothie))
s.add(z3.Distinct(hobbies))
for var in names + occupations + education + smoothie + hobbies:
    s.add(z3.And(0 <= var, var <= 2))

# Add specific constraints
# Clue 2: Arnold not in third house (names[2] != 0)
s.add(names[2] != 0)

# Clue 3: Cherry in house 3 (smoothie[2] = 1)
s.add(smoothie[2] == 1)

# Clue 4: cooking in house 2 (hobbies[1] = 1)
s.add(hobbies[1] == 1)

# Clue 5: Peter in house 2 (names[1] = 1)
s.add(names[1] == 1)

# Clue 8: doctor in house 2 (occupations[1] = 0)
s.add(occupations[1] == 0)

# Clue 1: Desert lover (smoothie[1] = 0)
s.add(smoothie[1] == 0)

# Clue 7: bachelor's degree in house 3 (education[2] == 2)
s.add(education[2] == 2)

# Clue 6: gardening hobby before associate education
i_gardening = z3.If(hobbies[0] == 0, 0, z3.If(hobbies[1] == 0, 1, 2))
i_associate = z3.If(education[0] == 0, 0, z3.If(education[1] == 0, 1, 2))
s.add(i_gardening < i_associate)

# Clue 9: photography hobby is teacher
for i in range(3):
    s.add(z3.Or(hobbies[i] != 2, occupations[i] == 1))

# Check satisfiability
if s.check() == z3.sat:
    model = s.model()
    # Mappings
    name_map = {0: 'Arnold', 1: 'Peter', 2: 'Eric'}
    occupation_map = {0: 'doctor', 1: 'teacher', 2: 'engineer'}
    education_map = {0: 'associate', 1: 'high school', 2: 'bachelor'}
    smoothie_map = {0: 'desert', 1: 'cherry', 2: 'watermelon'}
    hobby_map = {0: 'gardening', 1: 'cooking', 2: 'photography'}
    
    # Prepare rows
    rows = []
    for i in range(3):
        house_num = str(i + 1)
        name_val = name_map[model.eval(names[i]).as_long()]
        occ_val = occupation_map[model.eval(occupations[i]).as_long()]
        edu_val = education_map[model.eval(education[i]).as_long()]
        smooth_val = smoothie_map[model.eval(smoothie[i]).as_long()]
        hobby_val = hobby_map[model.eval(hobbies[i]).as_long()]
        rows.append([house_num, name_val, occ_val, edu_val, smooth_val, hobby_val])
    
    # Format as JSON
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")