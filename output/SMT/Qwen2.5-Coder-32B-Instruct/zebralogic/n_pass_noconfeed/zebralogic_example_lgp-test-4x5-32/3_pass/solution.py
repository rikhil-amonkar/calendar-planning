from z3 import *
import json

# Define the domains
names = ["Arnold", "Alice", "Eric", "Peter"]
hobbies = ["cooking", "painting", "photography", "gardening"]
birthdays = ["april", "jan", "sept", "feb"]
educations = ["master", "bachelor", "associate", "high school"]
smoothies = ["cherry", "watermelon", "desert", "dragonfruit"]

# Create a solver instance
solver = Solver()

# Define variables
house_vars = [Int(f"house_{i}") for i in range(1, 5)]
name_vars = {name: Int(f"name_{name}") for name in names}
hobby_vars = {hobby: Int(f"hobby_{hobby}") for hobby in hobbies}
birthday_vars = {birthday: Int(f"birthday_{birthday}") for birthday in birthdays}
education_vars = {education: Int(f"education_{education}") for education in educations}
smoothie_vars = {smoothie: Int(f"smoothie_{smoothie}") for smoothie in smoothies}

# Add domain constraints
for var in house_vars + list(name_vars.values()) + list(hobby_vars.values()) + list(birthday_vars.values()) + list(education_vars.values()) + list(smoothie_vars.values()):
    solver.add(var >= 1, var <= 4)

# All variables must be distinct
solver.add(Distinct(house_vars))
solver.add(Distinct(list(name_vars.values())))
solver.add(Distinct(list(hobby_vars.values())))
solver.add(Distinct(list(birthday_vars.values())))
solver.add(Distinct(list(education_vars.values())))
solver.add(Distinct(list(smoothie_vars.values())))

# Add clues as constraints
# 1. The Desert smoothie lover is the person whose birthday is in January.
solver.add(smoothie_vars["desert"] == birthday_vars["jan"])

# 2. Eric is the person with a bachelor's degree.
solver.add(name_vars["Eric"] == education_vars["bachelor"])

# 3. The person whose birthday is in January is the person with a bachelor's degree.
solver.add(birthday_vars["jan"] == education_vars["bachelor"])

# 4. The person with a high school diploma is in the third house.
solver.add(education_vars["high school"] == 3)

# 5. The Watermelon smoothie lover is not in the third house.
solver.add(smoothie_vars["watermelon"] != 3)

# 6. The person with an associate's degree is Arnold.
solver.add(education_vars["associate"] == name_vars["Arnold"])

# 7. The person with a master's degree is the person who paints as a hobby.
solver.add(education_vars["master"] == hobby_vars["painting"])

# 8. There is one house between the Dragonfruit smoothie lover and the person whose birthday is in September.
solver.add(Abs(smoothie_vars["dragonfruit"] - birthday_vars["sept"]) == 2)

# 9. The person with a high school diploma is the person whose birthday is in September.
solver.add(education_vars["high school"] == birthday_vars["sept"])

# 10. The person who loves cooking is Alice.
solver.add(hobby_vars["cooking"] == name_vars["Alice"])

# 11. The person whose birthday is in April and the person who enjoys gardening are next to each other.
solver.add(Abs(birthday_vars["april"] - hobby_vars["gardening"]) == 1)

# 12. The person who paints as a hobby is the person whose birthday is in February.
solver.add(hobby_vars["painting"] == birthday_vars["feb"])

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Extract the solution
    solution = []
    for house in range(1, 5):
        name = next(name for name, var in name_vars.items() if model.evaluate(var).as_long() == house)
        hobby = next(hobby for hobby, var in hobby_vars.items() if model.evaluate(var).as_long() == house)
        birthday = next(birthday for birthday, var in birthday_vars.items() if model.evaluate(var).as_long() == house)
        education = next(education for education, var in education_vars.items() if model.evaluate(var).as_long() == house)
        smoothie = next(smoothie for smoothie, var in smoothie_vars.items() if model.evaluate(var).as_long() == house)
        solution.append([str(house), name, hobby, birthday, education, smoothie])
    
    # Output the solution as JSON
    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found")