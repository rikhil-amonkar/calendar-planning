from z3 import *
import json

def main():
    # Define the attribute lists
    names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    smoothies = ['lime', 'dragonfruit', 'desert', 'watermelon', 'cherry']
    animals = ['horse', 'dog', 'bird', 'fish', 'cat']
    nationalities = ['german', 'swede', 'norwegian', 'brit', 'dane']
    
    # Create enum sorts and their constants
    Name, (Alice, Peter, Bob, Eric, Arnold) = EnumSort('Name', names)
    Smoothie, (lime, dragonfruit, desert, watermelon, cherry) = EnumSort('Smoothie', smoothies)
    Animal, (horse, dog, bird, fish, cat) = EnumSort('Animal', animals)
    Nationality, (german, swede, norwegian, brit, dane) = EnumSort('Nationality', nationalities)
    
    # Create lists of the constants for easy access
    name_consts = [Alice, Peter, Bob, Eric, Arnold]
    smoothie_consts = [lime, dragonfruit, desert, watermelon, cherry]
    animal_consts = [horse, dog, bird, fish, cat]
    nationality_consts = [german, swede, norwegian, brit, dane]
    
    # Create Z3 variables for each house (0-indexed: house0, house1, ... house4)
    n = [Const('n%d' % i, Name) for i in range(5)]
    s = [Const('s%d' % i, Smoothie) for i in range(5)]
    a = [Const('a%d' % i, Animal) for i in range(5)]
    nat = [Const('nat%d' % i, Nationality) for i in range(5)]
    
    s_solver = Solver()
    
    # Each attribute must be unique per house
    s_solver.add(Distinct(n))
    s_solver.add(Distinct(s))
    s_solver.add(Distinct(a))
    s_solver.add(Distinct(nat))
    
    # Clue 1: The Swedish person is directly left of the dog owner.
    for i in range(4):
        s_solver.add(Implies(nat[i] == swede, a[i+1] == dog))
    
    # Clue 2: There are two houses between the dog owner and the British person.
    # |index_dog - index_brit| = 3
    pairs = [(0,3), (3,0), (1,4), (4,1)]
    s_solver.add(Or([And(a[i] == dog, nat[j] == brit) for (i,j) in pairs]))
    
    # Clue 3: The Dane is the person who keeps horses.
    for i in range(5):
        s_solver.add(Implies(nat[i] == dane, a[i] == horse))
    
    # Clue 4: The bird keeper is somewhere to the right of the cat lover.
    # Therefore, cat cannot be in the last house (house5, index4) because there is no house to the right.
    s_solver.add(a[4] != cat)
    for i in range(4):
        s_solver.add(Implies(a[i] == cat, Or([a[j] == bird for j in range(i+1,5)])))
    
    # Clue 5: The dog owner is directly left of the person who drinks Lime smoothies.
    for i in range(4):
        s_solver.add(Implies(a[i] == dog, s[i+1] == lime))
    
    # Clue 6: Eric is the cat lover.
    for i in range(5):
        s_solver.add(Implies(n[i] == Eric, a[i] == cat))
    
    # Clue 7: Bob is the bird keeper.
    for i in range(5):
        s_solver.add(Implies(n[i] == Bob, a[i] == bird))
    
    # Clue 8: The person who likes Cherry smoothies is directly left of Peter.
    for i in range(4):
        s_solver.add(Implies(s[i] == cherry, n[i+1] == Peter))
    
    # Clue 9: The bird keeper is the Watermelon smoothie lover.
    for i in range(5):
        s_solver.add(Implies(a[i] == bird, s[i] == watermelon))
    
    # Clue 10: The Desert smoothie lover is the dog owner.
    for i in range(5):
        s_solver.add(Implies(s[i] == desert, a[i] == dog))
    
    # Clue 11: The person who keeps horses is in the third house (index2).
    s_solver.add(a[2] == horse)
    
    # Clue 12: The Norwegian is Alice.
    for i in range(5):
        s_solver.add(Implies(nat[i] == norwegian, n[i] == Alice))
    
    # Check for a solution
    if s_solver.check() == sat:
        m = s_solver.model()
        # Prepare the result structure
        result = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
                "rows": []
            }
        }
        # For each house, extract the attributes
        for i in range(5):
            house_num = str(i+1)
            # Get the name
            name_val = m.eval(n[i])
            name_str = names[name_consts.index(name_val)]
            # Get the smoothie
            smoothie_val = m.eval(s[i])
            smoothie_str = smoothies[smoothie_consts.index(smoothie_val)]
            # Get the animal
            animal_val = m.eval(a[i])
            animal_str = animals[animal_consts.index(animal_val)]
            # Get the nationality
            nat_val = m.eval(nat[i])
            nat_str = nationalities[nationality_consts.index(nat_val)]
            
            row = [house_num, name_str, smoothie_str, animal_str, nat_str]
            result["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == '__main__':
    main()