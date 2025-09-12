from z3 import *
import json

# Define EnumSorts for each category
Name, (Eric, Arnold, Peter) = EnumSort('Name', ['Eric', 'Arnold', 'Peter'])
Vacation, (mountain, city, beach) = EnumSort('Vacation', ['mountain', 'city', 'beach'])
Height, (vs, avg, sh) = EnumSort('Height', ['very short', 'average', 'short'])
Flower, (carnations, daffodils, lilies) = EnumSort('Flower', ['carnations', 'daffodils', 'lilies'])
HairColor, (brown, black, blonde) = EnumSort('HairColor', ['brown', 'black', 'blonde'])
Education, (associate, bachelor, highschool) = EnumSort('Education', ['associate', 'bachelor', 'high school'])

# Create variables for each house and each attribute
# House 1
name_1 = Const('name_1', Name)
vacation_1 = Const('vacation_1', Vacation)
height_1 = Const('height_1', Height)
flower_1 = Const('flower_1', Flower)
haircolor_1 = Const('haircolor_1', HairColor)
education_1 = Const('education_1', Education)

# House 2
name_2 = Const('name_2', Name)
vacation_2 = Const('vacation_2', Vacation)
height_2 = Const('height_2', Height)
flower_2 = Const('flower_2', Flower)
haircolor_2 = Const('haircolor_2', HairColor)
education_2 = Const('education_2', Education)

# House 3
name_3 = Const('name_3', Name)
vacation_3 = Const('vacation_3', Vacation)
height_3 = Const('height_3', Height)
flower_3 = Const('flower_3', Flower)
haircolor_3 = Const('haircolor_3', HairColor)
education_3 = Const('education_3', Education)

s = Solver()

# Add constraints for uniqueness in each category
s.add(Distinct(name_1, name_2, name_3))
s.add(Distinct(vacation_1, vacation_2, vacation_3))
s.add(Distinct(height_1, height_2, height_3))
s.add(Distinct(flower_1, flower_2, flower_3))
s.add(Distinct(haircolor_1, haircolor_2, haircolor_3))
s.add(Distinct(education_1, education_2, education_3))

# Add clues as constraints
# Clue 1: Peter is average height
s.add(Implies(name_1 == Peter, height_1 == avg))
s.add(Implies(name_2 == Peter, height_2 == avg))
s.add(Implies(name_3 == Peter, height_3 == avg))

# Clue 2: Arnold loves daffodils
s.add(Implies(name_1 == Arnold, flower_1 == daffodils))
s.add(Implies(name_2 == Arnold, flower_2 == daffodils))
s.add(Implies(name_3 == Arnold, flower_3 == daffodils))

# Clue 3: very short not in house 2
s.add(height_2 != vs)

# Clue 4: beach in house 1
s.add(vacation_1 == beach)

# Clue 5: high school in house 3
s.add(education_3 == highschool)

# Clue 6: short is to the right of very short
h_very_short = Int('h_very_short')
h_short = Int('h_short')
s.add(
    Or(
        And(h_very_short == 1, height_1 == vs),
        And(h_very_short == 2, height_2 == vs),
        And(h_very_short == 3, height_3 == vs)
    )
)
s.add(
    Or(
        And(h_short == 1, height_1 == sh),
        And(h_short == 2, height_2 == sh),
        And(h_short == 3, height_3 == sh)
    )
)
s.add(h_short > h_very_short)

# Clue 7: Eric loves lilies
s.add(Implies(name_1 == Eric, flower_1 == lilies))
s.add(Implies(name_2 == Eric, flower_2 == lilies))
s.add(Implies(name_3 == Eric, flower_3 == lilies))

# Clue 8: lilies lover has bachelor
s.add(Implies(flower_1 == lilies, education_1 == bachelor))
s.add(Implies(flower_2 == lilies, education_2 == bachelor))
s.add(Implies(flower_3 == lilies, education_3 == bachelor))

# Clue 9: city is to the right of Peter
h_peter = Int('h_peter')
h_city = Int('h_city')
s.add(
    Or(
        And(h_peter == 1, name_1 == Peter),
        And(h_peter == 2, name_2 == Peter),
        And(h_peter == 3, name_3 == Peter)
    )
)
s.add(
    Or(
        And(h_city == 1, vacation_1 == city),
        And(h_city == 2, vacation_2 == city),
        And(h_city == 3, vacation_3 == city)
    )
)
s.add(h_city > h_peter)

# Clue 10: blonde in third house
s.add(haircolor_3 == blonde)

# Clue 11: beach vacation has brown hair
s.add(Implies(vacation_1 == beach, haircolor_1 == brown))
s.add(Implies(vacation_2 == beach, haircolor_2 == brown))
s.add(Implies(vacation_3 == beach, haircolor_3 == brown))

if s.check() == sat:
    model = s.model()
    rows = []
    for house_num in [1, 2, 3]:
        if house_num == 1:
            name_var = name_1
            vacation_var = vacation_1
            height_var = height_1
            flower_var = flower_1
            haircolor_var = haircolor_1
            education_var = education_1
        elif house_num == 2:
            name_var = name_2
            vacation_var = vacation_2
            height_var = height_2
            flower_var = flower_2
            haircolor_var = haircolor_2
            education_var = education_2
        else:
            name_var = name_3
            vacation_var = vacation_3
            height_var = height_3
            flower_var = flower_3
            haircolor_var = haircolor_3
            education_var = education_3

        name = model[name_var]
        vacation = model[vacation_var]
        height = model[height_var]
        flower = model[flower_var]
        haircolor = model[haircolor_var]
        education = model[education_var]

        name_str = name.decl().name()
        vacation_str = vacation.decl().name()
        height_str = height.decl().name()
        flower_str = flower.decl().name()
        haircolor_str = haircolor.decl().name()
        education_str = education.decl().name()

        rows.append([str(house_num), name_str, vacation_str, height_str, flower_str, haircolor_str, education_str])

    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
            "rows": rows
        }
    }

    print(json.dumps(solution, indent=2))