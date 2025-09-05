import json
from z3 import *

def main():
    solver = Solver()
    houses = [1, 2, 3, 4, 5]
    
    # Define enums
    Name, (Arnold, Eric, Bob, Peter, Alice) = EnumSort('Name', ['Arnold', 'Eric', 'Bob', 'Peter', 'Alice'])
    Smoothie, (desert, watermelon, lime, cherry, dragonfruit) = EnumSort('Smoothie', ['desert', 'watermelon', 'lime', 'cherry', 'dragonfruit'])
    Nationality, (german, swede, norwegian, dane, brit) = EnumSort('Nationality', ['german', 'swede', 'norwegian', 'dane', 'brit'])
    
    # Create variables
    names = [Const(f'name_{i}', Name) for i in houses]
    smoothies = [Const(f'smoothie_{i}', Smoothie) for i in houses]
    nationalities = [Const(f'nationality_{i}', Nationality) for i in houses]
    
    # All attributes are permutations
    solver.add(Distinct(names))
    solver.add(Distinct(smoothies))
    solver.add(Distinct(nationalities))
    
    # Clue 2: Dragonfruit in second house
    solver.add(smoothies[1] == dragonfruit)
    
    # Clue 10: Alice in third house
    solver.add(names[2] == Alice)
    
    # Clue 11: Watermelon in third house
    solver.add(smoothies[2] == watermelon)
    
    # Clue 9: Alice is Norwegian
    solver.add(nationalities[2] == norwegian)
    
    # Clue 8: Bob is Dane
    for i in houses:
        solver.add(Implies(names[i-1] == Bob, nationalities[i-1] == dane))
    
    # Clue 3: Peter not in first house
    solver.add(names[0] != Peter)
    
    # Clue 5: Desert not in fifth house
    solver.add(smoothies[4] != desert)
    
    # Clue 4: Dane and Brit adjacent
    for i in range(4):
        solver.add(Or(
            And(nationalities[i] == dane, nationalities[i+1] == brit),
            And(nationalities[i] == brit, nationalities[i+1] == dane)
        ))
    
    # Clue 6: Swede left of Dragonfruit (which is in house 2)
    solver.add(Or(nationalities[0] == swede, nationalities[1] == swede))
    
    # Clue 7: Two houses between Lime and Dane
    dane_house = Int('dane_house')
    solver.add(dane_house >= 1, dane_house <= 5)
    for i in range(5):
        solver.add(Implies(nationalities[i] == dane, dane_house == i+1))
    
    lime_house = Int('lime_house')
    solver.add(lime_house >= 1, lime_house <= 5)
    for i in range(5):
        solver.add(Implies(smoothies[i] == lime, lime_house == i+1))
    
    solver.add(Abs(dane_house - lime_house) == 3)
    
    # Clue 1: Dragonfruit left of Eric
    dragonfruit_house = 2  # From clue 2
    for i in houses:
        solver.add(Implies(names[i-1] == Eric, i > dragonfruit_house))
    
    # Check solution
    if solver.check() == sat:
        model = solver.model()
        result = []
        for i in range(5):
            name_val = model.eval(names[i])
            smoothie_val = model.eval(smoothies[i])
            nationality_val = model.eval(nationalities[i])
            result.append([
                str(i+1),
                str(name_val),
                str(smoothie_val),
                str(nationality_val)
            ])
        
        output = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Nationality"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()