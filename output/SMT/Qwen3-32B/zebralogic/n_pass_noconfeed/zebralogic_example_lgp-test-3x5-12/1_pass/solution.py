from z3 import *

def main():
    # Define EnumSorts
    Names, (Eric, Peter, Arnold) = EnumSort('Names', ['Eric', 'Peter', 'Arnold'])
    Cigars, (BlueMaster, Prince, PallMall) = EnumSort('Cigars', ['BlueMaster', 'Prince', 'PallMall'])
    Hobbies, (Photography, Gardening, Cooking) = EnumSort('Hobbies', ['Photography', 'Gardening', 'Cooking'])
    Education, (HighSchool, Associate, Bachelor) = EnumSort('Education', ['HighSchool', 'Associate', 'Bachelor'])
    Drinks, (Tea, Milk, Water) = EnumSort('Drinks', ['Tea', 'Milk', 'Water'])

    # Create variables for each house (0-based index for 1,2,3 houses)
    name_1 = Const('name_1', Names)
    name_2 = Const('name_2', Names)
    name_3 = Const('name_3', Names)
    names = [name_1, name_2, name_3]

    cigar_1 = Const('cigar_1', Cigars)
    cigar_2 = Const('cigar_2', Cigars)
    cigar_3 = Const('cigar_3', Cigars)
    cigars = [cigar_1, cigar_2, cigar_3]

    hobby_1 = Const('hobby_1', Hobbies)
    hobby_2 = Const('hobby_2', Hobbies)
    hobby_3 = Const('hobby_3', Hobbies)
    hobbies = [hobby_1, hobby_2, hobby_3]

    education_1 = Const('education_1', Education)
    education_2 = Const('education_2', Education)
    education_3 = Const('education_3', Education)
    educations = [education_1, education_2, education_3]

    drink_1 = Const('drink_1', Drinks)
    drink_2 = Const('drink_2', Drinks)
    drink_3 = Const('drink_3', Drinks)
    drinks = [drink_1, drink_2, drink_3]

    s = Solver()

    # Add distinct constraints for each category
    s.add(Distinct(names))
    s.add(Distinct(cigars))
    s.add(Distinct(hobbies))
    s.add(Distinct(educations))
    s.add(Distinct(drinks))

    # Add clues
    # Clue 1: The person partial to Pall Mall is Peter.
    for i in range(3):
        s.add(Implies(cigars[i] == PallMall, names[i] == Peter))

    # Clue 2: Milk drinker directly left of high school
    s.add(Implies(drinks[0] == Milk, educations[1] == HighSchool))
    s.add(Implies(drinks[1] == Milk, educations[2] == HighSchool))
    s.add(Or(drinks[0] == Milk, drinks[1] == Milk))  # Milk can't be in house 3

    # Clue 3: Eric is tea drinker
    for i in range(3):
        s.add(Implies(names[i] == Eric, drinks[i] == Tea))

    # Clue 4: Arnold and Prince smoker are next to each other
    s.add(Implies(names[0] == Arnold, cigars[1] == Prince))
    s.add(Implies(names[1] == Arnold, Or(cigars[0] == Prince, cigars[2] == Prince)))
    s.add(Implies(names[2] == Arnold, cigars[1] == Prince))

    # Clue 5: Gardening is left of Prince smoker
    for i in range(3):
        for j in range(3):
            cond = And(hobbies[i] == Gardening, cigars[j] == Prince)
            s.add(Implies(cond, i < j))

    # Clue 6: Milk drinker has associate
    for i in range(3):
        s.add(Implies(drinks[i] == Milk, educations[i] == Associate))

    # Clue 7: Bachelor directly left of photography
    s.add(Implies(educations[0] == Bachelor, hobbies[1] == Photography))
    s.add(Implies(educations[1] == Bachelor, hobbies[2] == Photography))

    # Check solution
    if s.check() == sat:
        model = s.model()

        # Mapping from Enum constants to strings
        name_map = {Eric: 'Eric', Peter: 'Peter', Arnold: 'Arnold'}
        cigar_map = {BlueMaster: 'blue master', Prince: 'prince', PallMall: 'pall mall'}
        hobby_map = {Photography: 'photography', Gardening: 'gardening', Cooking: 'cooking'}
        education_map = {HighSchool: 'high school', Associate: 'associate', Bachelor: 'bachelor'}
        drink_map = {Tea: 'tea', Milk: 'milk', Water: 'water'}

        rows = []
        for i in range(3):
            house_num = i + 1
            name = name_map[model[names[i]]]
            cigar = cigar_map[model[cigars[i]]]
            hobby = hobby_map[model[hobbies[i]]]
            education = education_map[model[educations[i]]]
            drink = drink_map[model[drinks[i]]]
            rows.append([str(house_num), name, cigar, hobby, education, drink])

        solution = {
            "solution": {
                "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
                "rows": rows
            }
        }

        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()