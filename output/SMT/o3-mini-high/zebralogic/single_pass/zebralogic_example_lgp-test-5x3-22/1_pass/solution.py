from z3 import *
import json

def main():
    s = Solver()

    # Create integer variables representing the house number (1 to 5) for each person.
    Arnold = Int('Arnold')
    Eric   = Int('Eric')
    Bob    = Int('Bob')
    Peter  = Int('Peter')
    Alice  = Int('Alice')
    
    # Create integer variables for each smoothie.
    desert      = Int('desert')
    watermelon  = Int('watermelon')
    lime        = Int('lime')
    cherry      = Int('cherry')
    dragonfruit = Int('dragonfruit')
    
    # Create integer variables for each nationality.
    german    = Int('german')
    swede     = Int('swede')
    norwegian = Int('norwegian')
    dane      = Int('dane')
    brit      = Int('brit')
    
    # All variables must be between 1 and 5.
    all_vars = [Arnold, Eric, Bob, Peter, Alice,
                desert, watermelon, lime, cherry, dragonfruit,
                german, swede, norwegian, dane, brit]
    for var in all_vars:
        s.add(var >= 1, var <= 5)
    
    # Each category must have a permutation of the houses.
    s.add(Distinct(Arnold, Eric, Bob, Peter, Alice))
    s.add(Distinct(desert, watermelon, lime, cherry, dragonfruit))
    s.add(Distinct(german, swede, norwegian, dane, brit))
    
    # Clue 2: The Dragonfruit smoothie lover is in the second house.
    s.add(dragonfruit == 2)
    
    # Clue 10: Alice is in the third house.
    s.add(Alice == 3)
    
    # Clue 11: The Watermelon smoothie lover is in the third house.
    s.add(watermelon == 3)
    
    # Clue 9: Alice is the Norwegian.
    s.add(Alice == norwegian)
    
    # Clue 8: Bob is the Dane.
    s.add(Bob == dane)
    
    # Clue 1: The Dragonfruit smoothie lover is somewhere to the left of Eric.
    s.add(dragonfruit < Eric)
    
    # Clue 3: Peter is not in the first house.
    s.add(Peter != 1)
    
    # Clue 4: The Dane and the British person are next to each other.
    s.add(Abs(dane - brit) == 1)
    
    # Clue 5: The Desert smoothie lover is not in the fifth house.
    s.add(desert != 5)
    
    # Clue 6: The Swedish person is somewhere to the left of the Dragonfruit smoothie lover.
    s.add(swede < dragonfruit)
    
    # Clue 7: There are two houses between the person who drinks Lime smoothies and the Dane.
    s.add(Abs(lime - dane) == 3)
    
    # Check if the constraints are satisfiable.
    if s.check() == sat:
        m = s.model()
        # Prepare a mapping from house number to its attributes.
        houses = {i: {"Name": None, "Smoothie": None, "Nationality": None} for i in range(1, 6)}
        
        # Get the assignment for each person.
        persons = [("Arnold", m[Arnold].as_long()),
                   ("Eric", m[Eric].as_long()),
                   ("Bob", m[Bob].as_long()),
                   ("Peter", m[Peter].as_long()),
                   ("Alice", m[Alice].as_long())]
                   
        for name, house in persons:
            houses[house]["Name"] = name
        
        # Get the assignment for each smoothie.
        smoothies = [("desert", m[desert].as_long()),
                     ("watermelon", m[watermelon].as_long()),
                     ("lime", m[lime].as_long()),
                     ("cherry", m[cherry].as_long()),
                     ("dragonfruit", m[dragonfruit].as_long())]
                     
        for smoothie, house in smoothies:
            houses[house]["Smoothie"] = smoothie
        
        # Get the assignment for each nationality.
        nationalities = [("german", m[german].as_long()),
                         ("swede", m[swede].as_long()),
                         ("norwegian", m[norwegian].as_long()),
                         ("dane", m[dane].as_long()),
                         ("brit", m[brit].as_long())]
                         
        for nat, house in nationalities:
            houses[house]["Nationality"] = nat
        
        # Build a list of rows in house order.
        rows = []
        for i in range(1, 6):
            rows.append([str(i), houses[i]["Name"], houses[i]["Smoothie"], houses[i]["Nationality"]])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Nationality"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()