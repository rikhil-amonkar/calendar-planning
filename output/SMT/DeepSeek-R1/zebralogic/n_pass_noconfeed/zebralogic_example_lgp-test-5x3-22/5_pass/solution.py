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
    adjacent_conditions = []
    for i in range(4):
        adjacent_conditions.append(And(nationalities[i] == dane, nationalities[i+1] == brit))
        adjacent_conditions.append(And(nationalities[i] == brit, nationalities[i+1] == dane))
    solver.add(Or(adjacent_conditions))
    
    # Clue 6: Swede left of Dragonfruit (house 2 index 1)
    solver.add(nationalities[0] == swede)
    
    # Clue 7: Two houses between Lime and Dane
    solver.add(Or(
        And(smoothies[0] == lime, nationalities[3] == dane),
        And(smoothies[3] == lime, nationalities[0] == dane),
        And(smoothies[1] == lime, nationalities[4] == dane),
        And(smoothies[4] == lime, nationalities[1] == dane)
    ))
    
    # Clue 1: Dragonfruit left of Eric
    # Since Dragonfruit is at index 1, Eric must be at index > 1
    eric_conditions = []
    for i in houses:
        if i > 1:
            eric_conditions.append(names[i] == Eric)
    solver.add(Or(eric_conditions))
    
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