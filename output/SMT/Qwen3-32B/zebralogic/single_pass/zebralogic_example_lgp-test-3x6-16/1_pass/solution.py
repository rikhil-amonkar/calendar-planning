import json
from z3 import *

# Define EnumSorts
Name, (Eric, Peter, Arnold) = EnumSort('Name', ['Eric', 'Peter', 'Arnold'])
Drink, (tea, water, milk) = EnumSort('Drink', ['tea', 'water', 'milk'])
Nationality, (dane, brit, swede) = EnumSort('Nationality', ['dane', 'brit', 'swede'])
Education, (highschool, associate, bachelor) = EnumSort('Education', ['high school', 'associate', 'bachelor'])
HouseStyle, (victorian, colonial, ranch) = EnumSort('HouseStyle', ['victorian', 'colonial', 'ranch'])
Smoothie, (cherry, watermelon, desert) = EnumSort('Smoothie', ['cherry', 'watermelon', 'desert'])

# Create variables for each house (1, 2, 3)
names = [Const(f'name_{i+1}', Name) for i in range(3)]
drinks = [Const(f'drink_{i+1}', Drink) for i in range(3)]
nationalities = [Const(f'nationality_{i+1}', Nationality) for i in range(3)]
educations = [Const(f'education_{i+1}', Education) for i in range(3)]
housestyles = [Const(f'housestyle_{i+1}', HouseStyle) for i in range(3)]
smoothies = [Const(f'smoothie_{i+1}', Smoothie) for i in range(3)]

s = Solver()

# Add distinctness constraints
s.add(Distinct(names))
s.add(Distinct(drinks))
s.add(Distinct(nationalities))
s.add(Distinct(educations))
s.add(Distinct(housestyles))
s.add(Distinct(smoothies))

# Add clues
# Clue 1: One house between Eric and tea
s.add(Or(And(names[0] == Eric, drinks[2] == tea), And(names[2] == Eric, drinks[0] == tea)))
s.add(names[1] != Eric)

# Clue 2: Milk drinker is in ranch-style home
for i in range(3):
    s.add(Implies(drinks[i] == milk, housestyles[i] == ranch))

# Clue 3: Bachelor's degree is in second house
s.add(educations[1] == bachelor)

# Clue 4: High school diploma is Dane
for i in range(3):
    s.add(Implies(educations[i] == highschool, nationalities[i] == dane))

# Clue 5: Desert smoothie lover is Swedish
for i in range(3):
    s.add(Implies(smoothies[i] == desert, nationalities[i] == swede))

# Clue 6: Victorian house is not first
s.add(housestyles[0] != victorian)

# Clue 7: Cherry smoothie lover is in colonial house
for i in range(3):
    s.add(Implies(smoothies[i] == cherry, housestyles[i] == colonial))

# Clue 8: Arnold is to the right of the Victorian house
arnold_house_num = If(names[0] == Arnold, 1, If(names[1] == Arnold, 2, 3))
victorian_house_num = If(housestyles[0] == victorian, 1, If(housestyles[1] == victorian, 2, 3))
s.add(arnold_house_num > victorian_house_num)

# Clue 9: Ranch-style home has high school education
for i in range(3):
    s.add(Implies(housestyles[i] == ranch, educations[i] == highschool))

if s.check() == sat:
    m = s.model()
    rows = []
    for i in range(3):
        house_num = i + 1
        name = str(m.evaluate(names[i]))
        drink = str(m.evaluate(drinks[i]))
        nationality = str(m.evaluate(nationalities[i]))
        education = str(m.evaluate(educations[i]))
        housestyle = str(m.evaluate(housestyles[i]))
        smoothie = str(m.evaluate(smoothies[i]))
        rows.append([str(house_num), name, drink, nationality, education, housestyle, smoothie])
    solution = {
        "solution": {
            "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")