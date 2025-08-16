from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = [1, 2, 3, 4]
names = ['Arnold', 'Alice', 'Eric', 'Peter']
hobbies = ['cooking', 'painting', 'photography', 'gardening']
birthdays = ['april', 'jan', 'sept', 'feb']
educations = ['master', 'bachelor', 'associate', 'high school']
smoothies = ['cherry', 'watermelon', 'desert', 'dragonfruit']

# Create dictionaries to map variables to Z3 variables
name_vars = {house: Int(f'name_{house}') for house in houses}
hobby_vars = {house: Int(f'hobby_{house}') for house in houses}
birthday_vars = {house: Int(f'birthday_{house}') for house in houses}
education_vars = {house: Int(f'education_{house}') for house in houses}
smoothie_vars = {house: Int(f'smoothie_{house}') for house in houses}

# Add constraints for uniqueness within each category
for house in houses:
    solver.add(name_vars[house] >= 0, name_vars[house] < len(names))
    solver.add(hobby_vars[house] >= 0, hobby_vars[house] < len(hobbies))
    solver.add(birthday_vars[house] >= 0, birthday_vars[house] < len(birthdays))
    solver.add(education_vars[house] >= 0, education_vars[house] < len(educations))
    solver.add(smoothie_vars[house] >= 0, smoothie_vars[house] < len(smoothies))

solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([hobby_vars[house] for house in houses]))
solver.add(Distinct([birthday_vars[house] for house in houses]))
solver.add(Distinct([education_vars[house] for house in houses]))
solver.add(Distinct([smoothie_vars[house] for house in houses]))

# Add specific clues
# Clue 1 & 3: The Desert smoothie lover is the person whose birthday is in January.
# Clue 3: The person whose birthday is in January is the person with a bachelor's degree.
solver.add(smoothie_vars[houses[birthdays.index('jan')]] == smoothies.index('desert'))
solver.add(birthday_vars[houses[educations.index('bachelor')]] == birthdays.index('jan'))

# Clue 4: The person with a high school diploma is in the third house.
solver.add(education_vars[3] == educations.index('high school'))

# Clue 5: The Watermelon smoothie lover is not in the third house.
solver.add(smoothie_vars[3] != smoothies.index('watermelon'))

# Clue 6: The person with an associate's degree is Arnold.
solver.add(education_vars[houses[names.index('Arnold')]] == educations.index('associate'))

# Clue 7: The person with a master's degree is the person who paints as a hobby.
solver.add(education_vars[houses[hobbies.index('painting')]] == educations.index('master'))

# Clue 8: There is one house between the Dragonfruit smoothie lover and the person whose birthday is in September.
solver.add(Abs(birthday_vars[houses[smoothies.index('dragonfruit')]] - birthday_vars[houses[birthdays.index('sept')]]) == 1)

# Clue 9: The person with a high school diploma is the person whose birthday is in September.
solver.add(birthday_vars[houses[educations.index('high school')]] == birthdays.index('sept'))

# Clue 10: The person who loves cooking is Alice.
solver.add(smoothie_vars[houses[names.index('Alice')]] == smoothies.index('cooking'))

# Clue 11: The person whose birthday is in April and the person who enjoys gardening are next to each other.
solver.add(Abs(birthday_vars[houses[hobbies.index('gardening')]] - birthday_vars[houses[birthdays.index('april')]]) == 1)

# Clue 12: The person who paints as a hobby is the person whose birthday is in February.
solver.add(hobby_vars[houses[birthdays.index('feb')]] == hobbies.index('painting'))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        hobby = hobbies[model[hobby_vars[house]].as_long()]
        birthday = birthdays[model[birthday_vars[house]].as_long()]
        education = educations[model[education_vars[house]].as_long()]
        smoothie = smoothies[model[smoothie_vars[house]].as_long()]
        solution["solution"]["rows"].append([str(house), name, hobby, birthday, education, smoothie])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")