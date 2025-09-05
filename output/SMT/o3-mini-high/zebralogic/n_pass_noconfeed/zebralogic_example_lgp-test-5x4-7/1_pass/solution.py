import json
from z3 import *

def main():
    s = Solver()

    # Create Int variables for each attribute with domain 1..5
    # Names
    alice = Int('alice')
    peter = Int('peter')
    bob = Int('bob')
    eric = Int('eric')
    arnold = Int('arnold')
    
    # Smoothies
    lime = Int('lime')
    dragonfruit = Int('dragonfruit')
    desert = Int('desert')
    watermelon = Int('watermelon')
    cherry = Int('cherry')
    
    # Animals
    horse = Int('horse')
    dog = Int('dog')
    bird = Int('bird')
    fish = Int('fish')
    cat = Int('cat')
    
    # Nationalities
    german = Int('german')
    swede = Int('swede')
    norwegian = Int('norwegian')
    brit = Int('brit')
    dane = Int('dane')
    
    # All variables in one list for domain constraints
    vars_all = [alice, peter, bob, eric, arnold,
                lime, dragonfruit, desert, watermelon, cherry,
                horse, dog, bird, fish, cat,
                german, swede, norwegian, brit, dane]
    for var in vars_all:
        s.add(var >= 1, var <= 5)
    
    # Each category must be a permutation of houses 1 to 5
    s.add(Distinct(alice, peter, bob, eric, arnold))
    s.add(Distinct(lime, dragonfruit, desert, watermelon, cherry))
    s.add(Distinct(horse, dog, bird, fish, cat))
    s.add(Distinct(german, swede, norwegian, brit, dane))
    
    # Clue 1: The Swedish person is directly left of the dog owner.
    s.add(swede + 1 == dog)
    
    # Clue 2: There are two houses between the dog owner and the British person.
    s.add(Abs(dog - brit) == 3)
    
    # Clue 3: The Dane is the person who keeps horses.
    s.add(dane == horse)
    
    # Clue 4: The bird keeper is somewhere to the right of the cat lover.
    s.add(cat < bird)
    
    # Clue 5: The dog owner is directly left of the person who drinks Lime smoothies.
    s.add(dog + 1 == lime)
    
    # Clue 6: Eric is the cat lover.
    s.add(eric == cat)
    
    # Clue 7: Bob is the bird keeper.
    s.add(bob == bird)
    
    # Clue 8: The person who likes Cherry smoothies is directly left of Peter.
    s.add(cherry + 1 == peter)
    
    # Clue 9: The bird keeper is the Watermelon smoothie lover.
    s.add(bird == watermelon)
    
    # Clue 10: The Desert smoothie lover is the dog owner.
    s.add(desert == dog)
    
    # Clue 11: The person who keeps horses is in the third house.
    s.add(horse == 3)
    
    # Clue 12: The Norwegian is Alice.
    s.add(norwegian == alice)
    
    if s.check() == sat:
        m = s.model()
        
        # Build a mapping from house number to its attributes.
        houses = {i: {"Name": None, "Smoothie": None, "Animal": None, "Nationality": None} for i in range(1, 6)}
        
        # Map Names
        namesVars = [
            ("Alice", m.evaluate(alice).as_long()),
            ("Peter", m.evaluate(peter).as_long()),
            ("Bob", m.evaluate(bob).as_long()),
            ("Eric", m.evaluate(eric).as_long()),
            ("Arnold", m.evaluate(arnold).as_long())
        ]
        for name, pos in namesVars:
            houses[pos]["Name"] = name
        
        # Map Smoothies
        smoothiesVars = [
            ("lime", m.evaluate(lime).as_long()),
            ("dragonfruit", m.evaluate(dragonfruit).as_long()),
            ("desert", m.evaluate(desert).as_long()),
            ("watermelon", m.evaluate(watermelon).as_long()),
            ("cherry", m.evaluate(cherry).as_long())
        ]
        for smoothie, pos in smoothiesVars:
            houses[pos]["Smoothie"] = smoothie
        
        # Map Animals
        animalsVars = [
            ("horse", m.evaluate(horse).as_long()),
            ("dog", m.evaluate(dog).as_long()),
            ("bird", m.evaluate(bird).as_long()),
            ("fish", m.evaluate(fish).as_long()),
            ("cat", m.evaluate(cat).as_long())
        ]
        for animal, pos in animalsVars:
            houses[pos]["Animal"] = animal
        
        # Map Nationalities
        natVars = [
            ("german", m.evaluate(german).as_long()),
            ("swede", m.evaluate(swede).as_long()),
            ("norwegian", m.evaluate(norwegian).as_long()),
            ("brit", m.evaluate(brit).as_long()),
            ("dane", m.evaluate(dane).as_long())
        ]
        for nat, pos in natVars:
            houses[pos]["Nationality"] = nat
        
        # Build rows in order by house (1 to 5)
        rows = []
        for i in range(1, 6):
            row = [
                str(i),
                houses[i]["Name"],
                houses[i]["Smoothie"],
                houses[i]["Animal"],
                houses[i]["Nationality"]
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()