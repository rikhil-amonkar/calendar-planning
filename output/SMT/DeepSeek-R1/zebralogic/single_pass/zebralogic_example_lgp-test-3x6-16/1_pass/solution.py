from z3 import *
import json

def main():
    # Define enums for each attribute
    NameSort, (Eric, Peter, Arnold) = EnumSort('Name', ['Eric', 'Peter', 'Arnold'])
    DrinkSort, (tea, water, milk) = EnumSort('Drink', ['tea', 'water', 'milk'])
    NationalitySort, (dane, brit, swede) = EnumSort('Nationality', ['dane', 'brit', 'swede'])
    EducationSort, (high_school, associate, bachelor) = EnumSort('Education', ['high school', 'associate', 'bachelor'])
    HouseStyleSort, (victorian, colonial, ranch) = EnumSort('HouseStyle', ['victorian', 'colonial', 'ranch'])
    SmoothieSort, (cherry, watermelon, desert) = EnumSort('Smoothie', ['cherry', 'watermelon', 'desert'])

    # Attributes for each house (0-indexed: house1=0, house2=1, house3=2)
    n = [Const('n1', NameSort), Const('n2', NameSort), Const('n3', NameSort)]
    d = [Const('d1', DrinkSort), Const('d2', DrinkSort), Const('d3', DrinkSort)]
    nat = [Const('nat1', NationalitySort), Const('nat2', NationalitySort), Const('nat3', NationalitySort)]
    ed = [Const('ed1', EducationSort), Const('ed2', EducationSort), Const('ed3', EducationSort)]
    hs = [Const('hs1', HouseStyleSort), Const('hs2', HouseStyleSort), Const('hs3', HouseStyleSort)]
    sm = [Const('sm1', SmoothieSort), Const('sm2', SmoothieSort), Const('sm3', SmoothieSort)]

    s = Solver()

    # All attributes must be distinct per category
    s.add(Distinct(n))
    s.add(Distinct(d))
    s.add(Distinct(nat))
    s.add(Distinct(ed))
    s.add(Distinct(hs))
    s.add(Distinct(sm))

    # Clue 1: One house between Eric and tea drinker
    s.add(Or(
        And(n[0] == Eric, d[2] == tea),
        And(n[2] == Eric, d[0] == tea)
    ))

    # Clue 2: Milk drinker is in ranch-style house
    for i in range(3):
        s.add((d[i] == milk) == (hs[i] == ranch))

    # Clue 3: Bachelor in second house
    s.add(ed[1] == bachelor)

    # Clue 4: High school diploma holder is Dane
    for i in range(3):
        s.add((ed[i] == high_school) == (nat[i] == dane))

    # Clue 5: Desert smoothie lover is Swedish
    for i in range(3):
        s.add((sm[i] == desert) == (nat[i] == swede))

    # Clue 6: Victorian house not in first house
    s.add(hs[0] != victorian)

    # Clue 7: Cherry smoothie lover in colonial-style house
    for i in range(3):
        s.add((sm[i] == cherry) == (hs[i] == colonial))

    # Clue 8: Arnold to the right of Victorian house
    s.add(Or(
        And(hs[0] == victorian, Or(n[1] == Arnold, n[2] == Arnold)),
        And(hs[1] == victorian, n[2] == Arnold)
    ))

    # Clue 9: Ranch-style house has high school diploma
    for i in range(3):
        s.add((hs[i] == ranch) == (ed[i] == high_school))

    # Check for solution
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(3):
            house_num = str(i+1)
            name_val = m[n[i]].decl().name()
            drink_val = m[d[i]].decl().name()
            nat_val = m[nat[i]].decl().name()
            ed_val = m[ed[i]].decl().name()
            hs_val = m[hs[i]].decl().name()
            sm_val = m[sm[i]].decl().name()
            row = [house_num, name_val, drink_val, nat_val, ed_val, hs_val, sm_val]
            rows.append(row)
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()