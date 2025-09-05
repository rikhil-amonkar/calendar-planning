from z3 import *
import json

def main():
    s = Solver()

    # Names
    Peter = Int("Peter")
    Arnold = Int("Arnold")
    Alice = Int("Alice")
    Eric = Int("Eric")

    # Flowers
    roses = Int("roses")
    daffodils = Int("daffodils")
    carnations = Int("carnations")
    lilies = Int("lilies")

    # Hobbies
    photography = Int("photography")
    painting = Int("painting")
    cooking = Int("cooking")
    gardening = Int("gardening")

    # Pets
    dog = Int("dog")
    fish = Int("fish")
    bird = Int("bird")
    cat = Int("cat")

    # Colors
    red = Int("red")
    yellow = Int("yellow")
    green = Int("green")
    white = Int("white")

    # House Styles
    craftsman = Int("craftsman")
    colonial = Int("colonial")
    ranch = Int("ranch")
    victorian = Int("victorian")

    # All variables must be in the range 1..4 (each value represents the house number)
    all_vars = [Peter, Arnold, Alice, Eric,
                roses, daffodils, carnations, lilies,
                photography, painting, cooking, gardening,
                dog, fish, bird, cat,
                red, yellow, green, white,
                craftsman, colonial, ranch, victorian]
    for var in all_vars:
        s.add(And(var >= 1, var <= 4))

    # Each category is a permutation of houses
    s.add(Distinct(Peter, Arnold, Alice, Eric))
    s.add(Distinct(roses, daffodils, carnations, lilies))
    s.add(Distinct(photography, painting, cooking, gardening))
    s.add(Distinct(dog, fish, bird, cat))
    s.add(Distinct(red, yellow, green, white))
    s.add(Distinct(craftsman, colonial, ranch, victorian))

    # Clue 1: The person in a Craftsman-style house is Arnold.
    s.add(Arnold == craftsman)
    # Clue 6: The person in a Craftsman-style house is in the second house.
    s.add(craftsman == 2)
    
    # Clue 2: The person who loves the rose bouquet is somewhere to the right of Peter.
    s.add(roses > Peter)
    
    # Clue 3: The photography enthusiast is the person who owns a dog.
    s.add(photography == dog)
    
    # Clue 4: The person who loves a bouquet of daffodils is not in the fourth house.
    s.add(daffodils != 4)
    
    # Clue 5: The person who loves the rose bouquet is the person whose favorite color is red.
    s.add(roses == red)
    
    # Clue 7: Eric is the person residing in a Victorian house.
    s.add(Eric == victorian)
    
    # Clue 8: The person with an aquarium of fish is the person who loves white.
    s.add(fish == white)
    
    # Clue 9: The person who loves cooking is somewhere to the right of the person whose favorite color is red.
    s.add(cooking > red)
    
    # Clue 10: The person who loves white is the person who loves a carnations arrangement.
    s.add(white == carnations)
    
    # Clue 11: The person who loves white is somewhere to the right of the person who enjoys gardening.
    s.add(white > gardening)
    
    # Clue 12: The person who loves a bouquet of daffodils is the person who loves yellow.
    s.add(daffodils == yellow)
    
    # Clue 13: The person living in a colonial-style house is the person whose favorite color is red.
    s.add(colonial == red)
    
    # Clue 14: The person who has a cat is Eric.
    s.add(cat == Eric)

    if s.check() == sat:
        m = s.model()
        # Prepare category mappings: each tuple holds (Z3 variable, attribute string)
        names = [(Peter, "Peter"), (Arnold, "Arnold"), (Alice, "Alice"), (Eric, "Eric")]
        flowers = [(roses, "roses"), (daffodils, "daffodils"), (carnations, "carnations"), (lilies, "lilies")]
        hobbies = [(photography, "photography"), (painting, "painting"), (cooking, "cooking"), (gardening, "gardening")]
        pets = [(dog, "dog"), (fish, "fish"), (bird, "bird"), (cat, "cat")]
        colors = [(red, "red"), (yellow, "yellow"), (green, "green"), (white, "white")]
        housestyles = [(craftsman, "craftsman"), (colonial, "colonial"), (ranch, "ranch"), (victorian, "victorian")]

        # Create a mapping for each house number (1 to 4)
        houses = {i: {"Name": None, "Flower": None, "Hobby": None, "Pet": None, "Color": None, "HouseStyle": None} for i in range(1, 5)}

        for var, label in names:
            houses[m.evaluate(var).as_long()]["Name"] = label
        for var, label in flowers:
            houses[m.evaluate(var).as_long()]["Flower"] = label
        for var, label in hobbies:
            houses[m.evaluate(var).as_long()]["Hobby"] = label
        for var, label in pets:
            houses[m.evaluate(var).as_long()]["Pet"] = label
        for var, label in colors:
            houses[m.evaluate(var).as_long()]["Color"] = label
        for var, label in housestyles:
            houses[m.evaluate(var).as_long()]["HouseStyle"] = label

        # Build the rows in ascending house order (house numbers as strings)
        rows = []
        for i in range(1, 5):
            row = [
                str(i),
                houses[i]["Name"],
                houses[i]["Flower"],
                houses[i]["Hobby"],
                houses[i]["Pet"],
                houses[i]["Color"],
                houses[i]["HouseStyle"]
            ]
            rows.append(row)

        result = {
            "solution": {
                "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()