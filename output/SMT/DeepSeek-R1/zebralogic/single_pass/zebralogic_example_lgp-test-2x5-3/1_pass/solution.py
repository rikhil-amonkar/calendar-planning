from z3 import Solver, Int, Distinct, And, sat

def main():
    # Create solver
    s = Solver()
    
    # Define variables for house 1
    n1 = Int('n1')  # name: 0=Eric, 1=Arnold
    h1 = Int('h1')  # hobby: 0=gardening, 1=photography
    b1 = Int('b1')  # book: 0=science fiction, 1=mystery
    m1 = Int('m1')  # music: 0=rock, 1=pop
    d1 = Int('d1')  # birthday: 0=april, 1=sept
    
    # Define variables for house 2
    n2 = Int('n2')
    h2 = Int('h2')
    b2 = Int('b2')
    m2 = Int('m2')
    d2 = Int('d2')
    
    # Each attribute must be 0 or 1
    s.add(And(n1 >= 0, n1 <= 1))
    s.add(And(h1 >= 0, h1 <= 1))
    s.add(And(b1 >= 0, b1 <= 1))
    s.add(And(m1 >= 0, m1 <= 1))
    s.add(And(d1 >= 0, d1 <= 1))
    s.add(And(n2 >= 0, n2 <= 1))
    s.add(And(h2 >= 0, h2 <= 1))
    s.add(And(b2 >= 0, b2 <= 1))
    s.add(And(m2 >= 0, m2 <= 1))
    s.add(And(d2 >= 0, d2 <= 1))
    
    # Distinct constraints for each attribute
    s.add(Distinct(n1, n2))
    s.add(Distinct(h1, h2))
    s.add(Distinct(b1, b2))
    s.add(Distinct(m1, m2))
    s.add(Distinct(d1, d2))
    
    # Clue 2: Arnold is not in the first house -> n1 != Arnold (1) -> n1=0, n2=1
    s.add(n1 == 0)
    s.add(n2 == 1)
    
    # Clue 5: The person who loves mystery books is in the first house -> b1=1
    s.add(b1 == 1)
    
    # Clue 1: The person who loves mystery books is the person who loves rock music -> since b1=1, then m1=0
    s.add(m1 == 0)
    
    # Clue 3: The person who loves mystery books is the person who enjoys gardening -> since b1=1, then h1=0
    s.add(h1 == 0)
    
    # Clue 4: The person whose birthday is in April is Arnold -> Arnold is in house2 (n2=1) so d2=0 (april)
    s.add(d2 == 0)
    
    # Check if solver has a solution
    if s.check() == sat:
        model = s.model()
        
        # Map integer values to strings
        names = {0: "Eric", 1: "Arnold"}
        hobbies = {0: "gardening", 1: "photography"}
        books = {0: "science fiction", 1: "mystery"}
        music = {0: "rock", 1: "pop"}
        birthdays = {0: "april", 1: "sept"}
        
        # Extract values for house1
        house1 = [
            "1",
            names[model.evaluate(n1).as_long()],
            hobbies[model.evaluate(h1).as_long()],
            books[model.evaluate(b1).as_long()],
            music[model.evaluate(m1).as_long()],
            birthdays[model.evaluate(d1).as_long()]
        ]
        
        # Extract values for house2
        house2 = [
            "2",
            names[model.evaluate(n2).as_long()],
            hobbies[model.evaluate(h2).as_long()],
            books[model.evaluate(b2).as_long()],
            music[model.evaluate(m2).as_long()],
            birthdays[model.evaluate(d2).as_long()]
        ]
        
        # Prepare JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
                "rows": [house1, house2]
            }
        }
        
        # Print the JSON
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()