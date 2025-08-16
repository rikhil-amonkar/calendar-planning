import json
from z3 import *

# Define EnumSorts
Name, (Eric, Peter, Arnold) = EnumSort('Name', ['Eric', 'Peter', 'Arnold'])
Cigar, (BlueMaster, Prince, PallMall) = EnumSort('Cigar', ['blue_master', 'prince', 'pall_mall'])
Hobby, (Photography, Gardening, Cooking) = EnumSort('Hobby', ['photography', 'gardening', 'cooking'])
Education, (HighSchool, Associate, Bachelor) = EnumSort('Education', ['high_school', 'associate', 'bachelor'])
Drink, (Tea, Milk, Water) = EnumSort('Drink', ['tea', 'milk', 'water'])

# Create variables for each house
# House 1
name_1 = Const('name_1', Name)
cigar_1 = Const('cigar_1', Cigar)
hobby_1 = Const('hobby_1', Hobby)
education_1 = Const('education_1', Education)
drink_1 = Const('drink_1', Drink)

# House 2
name_2 = Const('name_2', Name)
cigar_2 = Const('cigar_2', Cigar)
hobby_2 = Const('hobby_2', Hobby)
education_2 = Const('education_2', Education)
drink_2 = Const('drink_2', Drink)

# House 3
name_3 = Const('name_3', Name)
cigar_3 = Const('cigar_3', Cigar)
hobby_3 = Const('hobby_3', Hobby)
education_3 = Const('education_3', Education)
drink_3 = Const('drink_3', Drink)

s = Solver()

# Add distinct constraints for each category
s.add(Distinct(name_1, name_2, name_3))
s.add(Distinct(cigar_1, cigar_2, cigar_3))
s.add(Distinct(hobby_1, hobby_2, hobby_3))
s.add(Distinct(education_1, education_2, education_3))
s.add(Distinct(drink_1, drink_2, drink_3))

# Clue 1: Pall Mall is Peter
s.add((cigar_1 == PallMall) == (name_1 == Peter))
s.add((cigar_2 == PallMall) == (name_2 == Peter))
s.add((cigar_3 == PallMall) == (name_3 == Peter))

# Clue 2: Milk is directly left of high school
s.add(Or(And(drink_1 == Milk, education_2 == HighSchool), And(drink_2 == Milk, education_3 == HighSchool)))

# Clue 3: Eric drinks tea
s.add(If(name_1 == Eric, drink_1 == Tea, True))
s.add(If(name_2 == Eric, drink_2 == Tea, True))
s.add(If(name_3 == Eric, drink_3 == Tea, True))

# Clue 4: Arnold and Prince smoker are next to each other
s.add(Or(
    And(name_1 == Arnold, cigar_2 == Prince),
    And(name_2 == Arnold, cigar_3 == Prince),
    And(cigar_1 == Prince, name_2 == Arnold),
    And(cigar_2 == Prince, name_3 == Arnold)
))

# Clue 5: Gardening is left of Prince
s.add(Or(cigar_2 == Prince, cigar_3 == Prince))
s.add(Implies(cigar_2 == Prince, hobby_1 == Gardening))
s.add(Implies(cigar_3 == Prince, Or(hobby_1 == Gardening, hobby_2 == Gardening)))

# Clue 6: Milk drinker has associate degree
s.add(If(drink_1 == Milk, education_1 == Associate, True))
s.add(If(drink_2 == Milk, education_2 == Associate, True))
s.add(If(drink_3 == Milk, education_3 == Associate, True))

# Clue 7: Bachelor is directly left of photography
s.add(Or(
    And(education_1 == Bachelor, hobby_2 == Photography),
    And(education_2 == Bachelor, hobby_3 == Photography)
))

# Check for solution
if s.check() == sat:
    model = s.model()
    rows = []
    for house_num in [1, 2, 3]:
        idx = house_num - 1
        names = [name_1, name_2, name_3]
        cigars = [cigar_1, cigar_2, cigar_3]
        hobbies = [hobby_1, hobby_2, hobby_3]
        educations = [education_1, education_2, education_3]
        drinks = [drink_1, drink_2, drink_3]
        row = [
            str(house_num),
            model.eval(names[idx]).sexpr(),
            model.eval(cigars[idx]).sexpr(),
            model.eval(hobbies[idx]).sexpr(),
            model.eval(educations[idx]).sexpr(),
            model.eval(drinks[idx]).sexpr()
        ]
        rows.append(row)
    solution = {
        "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
        "rows": rows
    }
    print(json.dumps({"solution": solution}, indent=2))
else:
    print("No solution found.")