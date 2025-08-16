import json
from z3 import *

def main():
    # Define the enums for each attribute
    NameSort, (Eric, Peter, Arnold) = EnumSort('Name', ['Eric', 'Peter', 'Arnold'])
    CigarSort, (blue_master, prince, pall_mall) = EnumSort('Cigar', ['blue_master', 'prince', 'pall_mall'])
    HobbySort, (photography, gardening, cooking) = EnumSort('Hobby', ['photography', 'gardening', 'cooking'])
    EducationSort, (high_school, associate, bachelor) = EnumSort('Education', ['high_school', 'associate', 'bachelor'])
    DrinkSort, (tea, milk, water) = EnumSort('Drink', ['tea', 'milk', 'water'])

    # Create variables for each house and attribute
    n = [Const('n0', NameSort), Const('n1', NameSort), Const('n2', NameSort)]
    c = [Const('c0', CigarSort), Const('c1', CigarSort), Const('c2', CigarSort)]
    h = [Const('h0', HobbySort), Const('h1', HobbySort), Const('h2', HobbySort)]
    e = [Const('e0', EducationSort), Const('e1', EducationSort), Const('e2', EducationSort)]
    d = [Const('d0', DrinkSort), Const('d1', DrinkSort), Const('d2', DrinkSort)]

    s = Solver()

    # All attributes must be distinct across houses
    s.add(Distinct(n[0], n[1], n[2]))
    s.add(Distinct(c[0], c[1], c[2]))
    s.add(Distinct(h[0], h[1], h[2]))
    s.add(Distinct(e[0], e[1], e[2]))
    s.add(Distinct(d[0], d[1], d[2]))

    # Clue 1: Pall Mall smoker is Peter
    for i in range(3):
        s.add(Implies(c[i] == pall_mall, n[i] == Peter))

    # Clue 2: Milk drinker is directly left of high school diploma
    s.add(Or(
        And(d[0] == milk, e[1] == high_school),
        And(d[1] == milk, e[2] == high_school)
    ))

    # Clue 3: Eric is the tea drinker
    for i in range(3):
        s.add(Implies(n[i] == Eric, d[i] == tea))

    # Clue 4: Arnold and Prince smoker are adjacent
    s.add(Or(
        And(n[0] == Arnold, c[1] == prince),
        And(n[1] == Arnold, Or(c[0] == prince, c[2] == prince)),
        And(n[2] == Arnold, c[1] == prince)
    ))

    # Clue 5: Gardener is left of Prince smoker
    s.add(c[0] != prince)  # Prince cannot be in house 1
    s.add(Or(
        And(h[0] == gardening, Or(c[1] == prince, c[2] == prince)),
        And(h[1] == gardening, c[2] == prince)
    ))

    # Clue 6: Milk drinker has associate's degree
    for i in range(3):
        s.add((d[i] == milk) == (e[i] == associate))

    # Clue 7: Bachelor is directly left of photography enthusiast
    s.add(Or(
        And(e[0] == bachelor, h[1] == photography),
        And(e[1] == bachelor, h[2] == photography)
    ))

    # Check for solution
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(3):
            house_num = str(i+1)
            name_val = m.evaluate(n[i]).decl().name()
            cigar_val = m.evaluate(c[i]).decl().name().replace('_', ' ')
            hobby_val = m.evaluate(h[i]).decl().name()
            education_val = m.evaluate(e[i]).decl().name().replace('_', ' ')
            drink_val = m.evaluate(d[i]).decl().name()
            row = [house_num, name_val, cigar_val, hobby_val, education_val, drink_val]
            rows.append(row)
        
        result = {
            "solution": {
                "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()