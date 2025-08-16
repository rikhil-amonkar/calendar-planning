from z3 import *
import json

# Define EnumSorts for each attribute
Name, (Eric, Arnold, Peter) = EnumSort('Name', ['Eric', 'Arnold', 'Peter'])
Vacation, (mountain, city, beach) = EnumSort('Vacation', ['mountain', 'city', 'beach'])
Height, (very_short, average, short) = EnumSort('Height', ['very_short', 'average', 'short'])
Flower, (carnations, daffodils, lilies) = EnumSort('Flower', ['carnations', 'daffodils', 'lilies'])
HairColor, (brown, black, blonde) = EnumSort('HairColor', ['brown', 'black', 'blonde'])
Education, (associate, bachelor, high_school) = EnumSort('Education', ['associate', 'bachelor', 'high_school'])

# Create variables for each house
# House 1
n1 = Const('n1', Name)
v1 = Const('v1', Vacation)
h1 = Const('h1', Height)
f1 = Const('f1', Flower)
hc1 = Const('hc1', HairColor)
e1 = Const('e1', Education)

# House 2
n2 = Const('n2', Name)
v2 = Const('v2', Vacation)
h2 = Const('h2', Height)
f2 = Const('f2', Flower)
hc2 = Const('hc2', HairColor)
e2 = Const('e2', Education)

# House 3
n3 = Const('n3', Name)
v3 = Const('v3', Vacation)
h3 = Const('h3', Height)
f3 = Const('f3', Flower)
hc3 = Const('hc3', HairColor)
e3 = Const('e3', Education)

# Now add constraints for uniqueness per attribute
s = Solver()

# Names must be distinct
s.add(Distinct(n1, n2, n3))
# Vacations must be distinct
s.add(Distinct(v1, v2, v3))
# Heights must be distinct
s.add(Distinct(h1, h2, h3))
# Flowers must be distinct
s.add(Distinct(f1, f2, f3))
# Hair colors must be distinct
s.add(Distinct(hc1, hc2, hc3))
# Education must be distinct
s.add(Distinct(e1, e2, e3))

# Add clues
s.add(Implies(n1 == Peter, h1 == average))
s.add(Implies(n2 == Peter, h2 == average))
s.add(Implies(n3 == Peter, h3 == average))

s.add(Implies(n1 == Arnold, f1 == daffodils))
s.add(Implies(n2 == Arnold, f2 == daffodils))
s.add(Implies(n3 == Arnold, f3 == daffodils))

s.add(h2 != very_short)

s.add(v1 == beach)

s.add(e3 == high_school)

s.add(h1 == very_short)

s.add(Implies(n1 == Eric, f1 == lilies))
s.add(Implies(n2 == Eric, f2 == lilies))
s.add(Implies(n3 == Eric, f3 == lilies))

s.add(Implies(n1 == Eric, e1 == bachelor))
s.add(Implies(n2 == Eric, e2 == bachelor))
s.add(Implies(n3 == Eric, e3 == bachelor))

s.add(Not(n3 == Peter))

s.add(Implies(n1 == Peter, Or(v2 == city, v3 == city)))
s.add(Implies(n2 == Peter, v3 == city))

s.add(hc3 == blonde)
s.add(hc1 == brown)
s.add(hc2 == black)

# Check if the constraints are satisfiable
if s.check() == sat:
    model = s.model()
    # Prepare the rows
    names = [n1, n2, n3]
    vacations = [v1, v2, v3]
    heights = [h1, h2, h3]
    flowers = [f1, f2, f3]
    haircolors = [hc1, hc2, hc3]
    educations = [e1, e2, e3]
    rows = []
    for i in range(3):
        house_num = str(i + 1)
        name = model.eval(names[i]).as_string()
        vacation = model.eval(vacations[i]).as_string()
        height = model.eval(heights[i]).as_string()
        flower = model.eval(flowers[i]).as_string()
        haircolor = model.eval(haircolors[i]).as_string()
        education = model.eval(educations[i]).as_string()
        rows.append([house_num, name, vacation, height, flower, haircolor, education])
    # Output the JSON
    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")