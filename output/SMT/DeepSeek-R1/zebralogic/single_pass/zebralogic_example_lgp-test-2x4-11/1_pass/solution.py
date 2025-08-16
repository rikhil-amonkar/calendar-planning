from z3 import *
import json

def main():
    # Define enums for attributes
    Name, (Eric, Arnold) = EnumSort('Name', ['Eric', 'Arnold'])
    Hobby, (gardening, photography) = EnumSort('Hobby', ['gardening', 'photography'])
    Pet, (cat, dog) = EnumSort('Pet', ['cat', 'dog'])
    Height, (short, very_short) = EnumSort('Height', ['short', 'very_short'])
    
    # Variables for house 1
    n1 = Const('n1', Name)
    hb1 = Const('hb1', Hobby)
    p1 = Const('p1', Pet)
    ht1 = Const('ht1', Height)
    
    # Variables for house 2
    n2 = Const('n2', Name)
    hb2 = Const('hb2', Hobby)
    p2 = Const('p2', Pet)
    ht2 = Const('ht2', Height)
    
    s = Solver()
    
    # Each attribute is unique across houses
    s.add(Distinct(n1, n2))
    s.add(Distinct(hb1, hb2))
    s.add(Distinct(p1, p2))
    s.add(Distinct(ht1, ht2))
    
    # Clue 1: The very short person is the photography enthusiast.
    s.add(Or(
        And(ht1 == very_short, hb1 == photography),
        And(ht2 == very_short, hb2 == photography)
    ))
    
    # Clue 2: Eric is the person who is very short.
    s.add(Or(
        And(n1 == Eric, ht1 == very_short),
        And(n2 == Eric, ht2 == very_short)
    ))
    
    # Clue 3: The person with a cat is to the right of the very short person.
    s.add(ht1 == very_short)
    s.add(p2 == cat)
    
    if s.check() == sat:
        m = s.model()
        
        # Mapping from Z3 constants to strings
        name_map = { Eric: "Eric", Arnold: "Arnold" }
        hobby_map = { gardening: "gardening", photography: "photography" }
        pet_map = { cat: "cat", dog: "dog" }
        height_map = { short: "short", very_short: "very short" }
        
        # Extract values for house 1
        house1 = [
            "1",
            name_map[m[n1]],
            hobby_map[m[hb1]],
            pet_map[m[p1]],
            height_map[m[ht1]]
        ]
        
        # Extract values for house 2
        house2 = [
            "2",
            name_map[m[n2]],
            hobby_map[m[hb2]],
            pet_map[m[p2]],
            height_map[m[ht2]]
        ]
        
        # Construct the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Pet", "Height"],
                "rows": [house1, house2]
            }
        }
        
        # Output as JSON
        print(json.dumps(solution_dict))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()