import json
from z3 import *

def main():
    solver = Solver()
    houses = list(range(5))  # 0-indexed for easier list handling
    
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
    
    # Clue 2: Dragonfruit in second house (index 1)
    solver.add(smoothies[1] == dragonfruit)
    
    # Clue 10: Alice in third house (index 2)
    solver.add(names[2] == Alice)
    
    # Clue 11: Watermelon in third house (index 2)
    solver.add(smoothies[2] == watermelon)
    
    # Clue 9: Alice is Norwegian
    solver.add(nationalities[2] == norwegian)
    
    # Clue 8: Bob is Dane (equivalence)
    for i in houses:
        solver.add((names[i] == Bob) == (nationalities[i] == dane))
    
    # Clue 3: Peter not in first house (index 0)
    solver.add(names[0] != Peter)
    
    # Clue 5: Desert not in fifth house (index 4)
    solver.add(smoothies[4] != desert)
    
    # Clue 4: Dane and Brit adjacent
    for i in range(4):
        solver.add(Or(
            And(nationalities[i] == dane, nationalities[i+1] == brit),
            And(nationalities[i] == brit, nationalities[i+1] == dane)
        ))
    
    # Clue 6: Swede left of Dragonfruit (house 2 index 1)
    solver.add(nationalities[0] == swede)  # Only possible in first house
    
    # Clue 7: Two houses between Lime and Dane
    dane_indices = [i for i in houses if nationalities[i] == dane]
    lime_indices = [i for i in houses if smoothies[i] == lime]
    solver.add(Or([And(dane_idx == i, lime_idx == j) for i in houses for j in houses if abs(i - j) == 3] for dane_idx in dane_indices for lime_idx in lime_indices))
    
    # Clue 1: Dragonfruit left of Eric
    eric_house = [i for i in houses if names[i] == Eric][0]
    dragonfruit_house = 1  # From clue 2 (index 1)
    solver.add(eric_house > dragonfruit_house)
    
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