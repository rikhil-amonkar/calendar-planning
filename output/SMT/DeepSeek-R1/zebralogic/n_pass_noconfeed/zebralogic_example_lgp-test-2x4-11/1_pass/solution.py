import z3
import json

def main():
    # Create solver
    s = z3.Solver()
    
    # Define enums for attributes
    NameSort, (Eric, Arnold) = z3.EnumSort('Name', ['Eric', 'Arnold'])
    HobbySort, (gardening, photography) = z3.EnumSort('Hobby', ['gardening', 'photography'])
    PetSort, (cat, dog) = z3.EnumSort('Pet', ['cat', 'dog'])
    HeightSort, (short, very_short) = z3.EnumSort('Height', ['short', 'very short'])
    
    # Create variables for each house
    n1, n2 = z3.Consts('n1 n2', NameSort)
    h1, h2 = z3.Consts('h1 h2', HobbySort)
    p1, p2 = z3.Consts('p1 p2', PetSort)
    ht1, ht2 = z3.Consts('ht1 ht2', HeightSort)
    
    # All attributes are unique per category
    s.add(z3.Distinct(n1, n2))
    s.add(z3.Distinct(h1, h2))
    s.add(z3.Distinct(p1, p2))
    s.add(z3.Distinct(ht1, ht2))
    
    # Clue 1: The person who is very short is the photography enthusiast.
    s.add(z3.Implies(ht1 == very_short, h1 == photography))
    s.add(z3.Implies(ht2 == very_short, h2 == photography))
    
    # Clue 2: Eric is the person who is very short.
    s.add(z3.Implies(n1 == Eric, ht1 == very_short))
    s.add(z3.Implies(n2 == Eric, ht2 == very_short))
    
    # Clue 3: The person who has a cat is somewhere to the right of the person who is very short.
    s.add(ht1 == very_short)  # Very short must be in house 1
    s.add(p2 == cat)           # Cat must be in house 2
    
    # Check satisfiability
    if s.check() == z3.sat:
        m = s.model()
        
        # Mapping from Z3 values to strings
        name_map = {Eric: "Eric", Arnold: "Arnold"}
        hobby_map = {gardening: "gardening", photography: "photography"}
        pet_map = {cat: "cat", dog: "dog"}
        height_map = {short: "short", very_short: "very short"}
        
        # Retrieve values for house 1
        n1_val = m.eval(n1)
        h1_val = m.eval(h1)
        p1_val = m.eval(p1)
        ht1_val = m.eval(ht1)
        
        # Retrieve values for house 2
        n2_val = m.eval(n2)
        h2_val = m.eval(h2)
        p2_val = m.eval(p2)
        ht2_val = m.eval(ht2)
        
        # Build rows
        rows = [
            ["1", name_map[n1_val], hobby_map[h1_val], pet_map[p1_val], height_map[ht1_val]],
            ["2", name_map[n2_val], hobby_map[h2_val], pet_map[p2_val], height_map[ht2_val]]
        ]
        
        # Create solution dictionary
        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Pet", "Height"],
                "rows": rows
            }
        }
        
        # Output JSON
        print(json.dumps(solution))
    else:
        print('{"solution": {}}')

if __name__ == "__main__":
    main()