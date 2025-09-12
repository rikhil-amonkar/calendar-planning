import json
from z3 import *

def main():
    # Define EnumSorts
    names_enum, (Arnold, Alice, Eric, Peter) = EnumSort('Name', ['Arnold', 'Alice', 'Eric', 'Peter'])
    hobbies_enum, (cooking, painting, photography, gardening) = EnumSort('Hobby', ['cooking', 'painting', 'photography', 'gardening'])
    birthdays_enum, (april, jan, sept, feb) = EnumSort('Birthday', ['april', 'jan', 'sept', 'feb'])
    education_enum, (master, bachelor, associate, high_school) = EnumSort('Education', ['master', 'bachelor', 'associate', 'high school'])
    smoothies_enum, (cherry, watermelon, desert, dragonfruit) = EnumSort('Smoothie', ['cherry', 'watermelon', 'desert', 'dragonfruit'])

    # Create variables for each house (0-based index)
    names = [ Const(f'name_{i+1}', names_enum) for i in range(4) ]
    hobbies = [ Const(f'hobby_{i+1}', hobbies_enum) for i in range(4) ]
    birthdays = [ Const(f'birthday_{i+1}', birthdays_enum) for i in range(4) ]
    educations = [ Const(f'education_{i+1}', education_enum) for i in range(4) ]
    smoothies = [ Const(f'smoothie_{i+1}', smoothies_enum) for i in range(4) ]

    solver = Solver()

    # Add distinctness constraints
    solver.add(Distinct(names))
    solver.add(Distinct(hobbies))
    solver.add(Distinct(birthdays))
    solver.add(Distinct(educations))
    solver.add(Distinct(smoothies))

    # Clue 4: High school diploma is in third house (index 2)
    solver.add(educations[2] == high_school)

    # Clue 5: Watermelon not in third house
    solver.add(smoothies[2] != watermelon)

    # Clue 9: High school has birthday in Sept (third house, index 2)
    solver.add(birthdays[2] == sept)

    # Clue 8: Dragonfruit smoothie lover is in house 1 (index 0)
    solver.add(smoothies[0] == dragonfruit)

    # Clues 1, 2, 3: If birthday is jan, then education is bachelor, name is Eric, smoothie is desert
    for i in range(4):
        solver.add(Implies(birthdays[i] == jan, 
            And(educations[i] == bachelor, names[i] == Eric, smoothies[i] == desert)))

    # Clue 6: Associate's degree is Arnold
    solver.add(Or(
        And(educations[0] == associate, names[0] == Arnold),
        And(educations[1] == associate, names[1] == Arnold),
        And(educations[2] == associate, names[2] == Arnold),
        And(educations[3] == associate, names[3] == Arnold)
    ))

    # Clue 7: Master's degree implies painting hobby
    for i in range(4):
        solver.add(Implies(educations[i] == master, hobbies[i] == painting))

    # Clue 12: Painting hobby implies birthday is feb
    for i in range(4):
        solver.add(Implies(hobbies[i] == painting, birthdays[i] == feb))

    # Clue 10: Cooking is Alice
    solver.add(Or(
        And(hobbies[0] == cooking, names[0] == Alice),
        And(hobbies[1] == cooking, names[1] == Alice),
        And(hobbies[2] == cooking, names[2] == Alice),
        And(hobbies[3] == cooking, names[3] == Alice)
    ))

    # Clue 11: April and gardening are adjacent
    clue11 = []
    for i in range(3):  # 0,1,2
        a = And(birthdays[i] == april, hobbies[i+1] == gardening)
        b = And(birthdays[i+1] == april, hobbies[i] == gardening)
        clue11.append(Or(a, b))
    solver.add(Or(clue11))

    # Check solution
    if solver.check() == sat:
        model = solver.model()
        rows = []
        for i in range(4):
            house_num = i + 1
            # Evaluate each attribute
            name = model.evaluate(names[i]).decl().name()
            hobby = model.evaluate(hobbies[i]).decl().name()
            birthday = model.evaluate(birthdays[i]).decl().name()
            education = model.evaluate(educations[i]).decl().name()
            smoothie = model.evaluate(smoothies[i]).decl().name()
            # Fix education's 'high_school' to 'high school'
            if education == 'high_school':
                education = 'high school'
            rows.append([str(house_num), name, hobby, birthday, education, smoothie])
        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()