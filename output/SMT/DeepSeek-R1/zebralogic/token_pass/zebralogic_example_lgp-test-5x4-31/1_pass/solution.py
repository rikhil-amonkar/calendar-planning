import z3
import json

def main():
    solver = z3.Solver()
    house = [1, 2, 3, 4, 5]
    
    # Define enums for attributes
    Name = z3.EnumSort('Name', ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter'])
    name = z3.Const('name', Name)
    names = [z3.Const(f'name_{i}', Name) for i in house]
    
    Vacation = z3.EnumSort('Vacation', ['cruise', 'city', 'camping', 'beach', 'mountain'])
    vacation = z3.Const('vacation', Vacation)
    vacations = [z3.Const(f'vacation_{i}', Vacation) for i in house]
    
    Children = z3.EnumSort('Children', ['Bella', 'Samantha', 'Fred', 'Meredith', 'Timothy'])
    child = z3.Const('child', Children)
    children = [z3.Const(f'child_{i}', Children) for i in house]
    
    Nationality = z3.EnumSort('Nationality', ['dane', 'norwegian', 'brit', 'german', 'swede'])
    nationality = z3.Const('nationality', Nationality)
    nationalities = [z3.Const(f'nationality_{i}', Nationality) for i in house]
    
    # All attributes are distinct
    solver.add(z3.Distinct(names))
    solver.add(z3.Distinct(vacations))
    solver.add(z3.Distinct(children))
    solver.add(z3.Distinct(nationalities))
    
    # Each house has exactly one value per attribute
    for i in house:
        solver.add(z3.And(
            z3.IsName(names[i-1]),
            z3.IsVacation(vacations[i-1]),
            z3.IsChildren(children[i-1]),
            z3.IsNationality(nationalities[i-1])
        ))
    
    # Clue 1: The Norwegian is Peter.
    solver.add(z3.Exists([nationality, name], z3.And(
        z3.IsNorwegian(nationality),
        z3.IsPeter(name),
        nationality == name
    )))
    
    # Clue 2: The Swedish person is the person's child is named Bella.
    solver.add(z3.Exists([nationality, child], z3.And(
        z3.IsSwede(nationality),
        z3.IsBella(child),
        nationality == child
    )))
    
    # Clue 3: Beach vacation directly left of child Samantha
    for i in range(1, 5):
        solver.add(z3.Implies(
            z3.IsBeach(vacations[i-1]),
            z3.IsSamantha(children[i])
        ))
    
    # Clue 4: Child Bella not in second house
    solver.add(z3.Not(z3.IsBella(children[1])))
    
    # Clue 5: Alice is British
    solver.add(z3.Exists([name, nationality], z3.And(
        z3.IsAlice(name),
        z3.IsBrit(nationality),
        name == nationality
    )))
    
    # Clue 6: Cruise in first house
    solver.add(z3.IsCruise(vacations[0]))
    
    # Clue 7: Child Meredith in fourth house
    solver.add(z3.IsMeredith(children[3]))
    
    # Clue 8: Eric not in fifth house
    solver.add(z3.Not(z3.IsEric(names[4])))
    
    # Clue 9: Swede right of Norwegian
    norwegian_house = z3.Int('norwegian_house')
    swede_house = z3.Int('swede_house')
    solver.add(z3.And(
        z3.ForAll([nationality], z3.Implies(z3.IsNorwegian(nationality), nationality == norwegian_house)),
        z3.ForAll([nationality], z3.Implies(z3.IsSwede(nationality), nationality == swede_house)),
        swede_house > norwegian_house
    ))
    
    # Clue 10: One house between child Fred and city vacation
    fred_house = z3.Int('fred_house')
    city_house = z3.Int('city_house')
    solver.add(z3.And(
        z3.ForAll([child], z3.Implies(z3.IsFred(child), child == fred_house)),
        z3.ForAll([vacation], z3.Implies(z3.IsCity(vacation), vacation == city_house)),
        z3.Or(fred_house - city_house == 2, city_house - fred_house == 2)
    ))
    
    # Clue 11: Bob enjoys camping
    solver.add(z3.Exists([name, vacation], z3.And(
        z3.IsBob(name),
        z3.IsCamping(vacation),
        name == vacation
    )))
    
    # Clue 12: Dane in fifth house
    solver.add(z3.IsDane(nationalities[4]))
    
    # Clue 13: Camping not in fifth house
    solver.add(z3.Not(z3.IsCamping(vacations[4])))
    
    # Check and get solution
    if solver.check() == z3.sat:
        model = solver.model()
        result = []
        for i in range(5):
            house_num = str(i+1)
            n = model.eval(names[i])
            v = model.eval(vacations[i])
            c = model.eval(children[i])
            nat = model.eval(nationalities[i])
            result.append([house_num, str(n), str(v), str(c), str(nat)])
        
        output = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Children", "Nationality"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()