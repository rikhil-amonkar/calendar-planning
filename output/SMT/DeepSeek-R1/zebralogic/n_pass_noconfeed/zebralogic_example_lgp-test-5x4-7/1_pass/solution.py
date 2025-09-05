import json
from z3 import *

def main():
    # Define the enums and constants for each category
    Name, (Alice, Peter, Bob, Eric, Arnold) = EnumSort('Name', ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold'])
    Smoothie, (lime, dragonfruit, desert, watermelon, cherry) = EnumSort('Smoothie', ['lime', 'dragonfruit', 'desert', 'watermelon', 'cherry'])
    Animal, (horse, dog, bird, fish, cat) = EnumSort('Animal', ['horse', 'dog', 'bird', 'fish', 'cat'])
    Nationality, (german, swede, norwegian, brit, dane) = EnumSort('Nationality', ['german', 'swede', 'norwegian', 'brit', 'dane'])
    
    # Create arrays for each house (1-5) for each category
    n = [Const(f'n_{i}', Name) for i in range(1, 6)]
    s = [Const(f's_{i}', Smoothie) for i in range(1, 6)]
    a = [Const(f'a_{i}', Animal) for i in range(1, 6)]
    nat = [Const(f'nat_{i}', Nationality) for i in range(1, 6)]
    
    solver = Solver()
    
    # Add distinct constraints
    solver.add(Distinct(n))
    solver.add(Distinct(s))
    solver.add(Distinct(a))
    solver.add(Distinct(nat))
    
    # Clue 1: The Swedish person is directly left of the dog owner.
    solver.add(Or([And(nat[i] == swede, a[i+1] == dog) for i in range(4)]))
    
    # Clue 2: There are two houses between the dog owner and the British person.
    constraints2 = []
    for i in range(5):
        if i+3 < 5:
            constraints2.append(And(a[i] == dog, nat[i+3] == brit))
        if i-3 >= 0:
            constraints2.append(And(a[i] == dog, nat[i-3] == brit))
    solver.add(Or(constraints2))
    
    # Clue 3: The Dane is the person who keeps horses.
    solver.add(Or([And(nat[i] == dane, a[i] == horse) for i in range(5)]))
    
    # Clue 4: The bird keeper is somewhere to the right of the cat lover.
    solver.add(Or([And(a[i] == cat, a[j] == bird) for i in range(5) for j in range(5) if i < j]))
    
    # Clue 5: The dog owner is directly left of the person who drinks Lime smoothies.
    solver.add(Or([And(a[i] == dog, s[i+1] == lime) for i in range(4)]))
    
    # Clue 6: Eric is the cat lover.
    solver.add(Or([And(n[i] == Eric, a[i] == cat) for i in range(5)]))
    
    # Clue 7: Bob is the bird keeper.
    solver.add(Or([And(n[i] == Bob, a[i] == bird) for i in range(5)]))
    
    # Clue 8: The person who likes Cherry smoothies is directly left of Peter.
    solver.add(Or([And(s[i] == cherry, n[i+1] == Peter) for i in range(4)]))
    
    # Clue 9: The bird keeper is the Watermelon smoothie lover.
    solver.add(Or([And(a[i] == bird, s[i] == watermelon) for i in range(5)]))
    
    # Clue 10: The Desert smoothie lover is the dog owner.
    solver.add(Or([And(s[i] == desert, a[i] == dog) for i in range(5)]))
    
    # Clue 11: The person who keeps horses is in the third house.
    solver.add(a[2] == horse)
    
    # Clue 12: The Norwegian is Alice.
    solver.add(Or([And(nat[i] == norwegian, n[i] == Alice) for i in range(5)]))
    
    # Check and get the model
    if solver.check() == sat:
        model = solver.model()
        
        # Constants and their string representations
        name_consts = [Alice, Peter, Bob, Eric, Arnold]
        name_strs = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
        smoothie_consts = [lime, dragonfruit, desert, watermelon, cherry]
        smoothie_strs = ['lime', 'dragonfruit', 'desert', 'watermelon', 'cherry']
        animal_consts = [horse, dog, bird, fish, cat]
        animal_strs = ['horse', 'dog', 'bird', 'fish', 'cat']
        nationality_consts = [german, swede, norwegian, brit, dane]
        nationality_strs = ['german', 'swede', 'norwegian', 'brit', 'dane']
        
        rows = []
        for i in range(5):
            # Get the value for each category in the current house
            n_val = model.eval(n[i])
            s_val = model.eval(s[i])
            a_val = model.eval(a[i])
            nat_val = model.eval(nat[i])
            
            # Map the Z3 values to strings
            name = None
            for j, const in enumerate(name_consts):
                if model.eval(const) == n_val:
                    name = name_strs[j]
                    break
                    
            smoothie = None
            for j, const in enumerate(smoothie_consts):
                if model.eval(const) == s_val:
                    smoothie = smoothie_strs[j]
                    break
                    
            animal = None
            for j, const in enumerate(animal_consts):
                if model.eval(const) == a_val:
                    animal = animal_strs[j]
                    break
                    
            nationality = None
            for j, const in enumerate(nationality_consts):
                if model.eval(const) == nat_val:
                    nationality = nationality_strs[j]
                    break
                    
            rows.append([str(i+1), name, smoothie, animal, nationality])
        
        # Create the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
                "rows": rows
            }
        }
        
        # Output as JSON
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()