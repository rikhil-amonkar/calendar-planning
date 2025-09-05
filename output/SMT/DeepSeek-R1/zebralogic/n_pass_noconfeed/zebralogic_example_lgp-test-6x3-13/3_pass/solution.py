import json
from z3 import *

def main():
    # Define the attributes
    names = ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric']
    genres = ['romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction']
    occupations = ['artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer']
    
    # Create Z3 sorts and functions for each attribute
    Name = DeclareSort('Name')
    name_consts = [Function(n, Name) for n in names]
    Genre = DeclareSort('Genre')
    genre_consts = [Function(g, Genre) for g in genres]
    Occupation = DeclareSort('Occupation')
    occupation_consts = [Function(o, Occupation) for o in occupations]
    
    # Create variables for each house
    houses = [1, 2, 3, 4, 5, 6]
    name_vars = [Const(f"name_{i}", Name) for i in houses]
    genre_vars = [Const(f"genre_{i}", Genre) for i in houses]
    occupation_vars = [Const(f"occupation_{i}", Occupation) for i in houses]
    
    s = Solver()
    
    # Add distinctness for constants
    s.add(Distinct([nc() for nc in name_consts]))
    s.add(Distinct([gc() for gc in genre_consts]))
    s.add(Distinct([oc() for oc in occupation_consts]))
    
    # Each attribute must be unique (permutation)
    s.add(Distinct(name_vars))
    s.add(Distinct(genre_vars))
    s.add(Distinct(occupation_vars))
    
    # Extract specific values for constraints
    alice = name_consts[3]()
    bob = name_consts[0]()
    carol = name_consts[2]()
    eric = name_consts[5]()
    arnold = name_consts[1]()
    
    fantasy = genre_consts[4]()
    mystery = genre_consts[3]()
    biography = genre_consts[2]()
    historical_fiction = genre_consts[1]()
    science_fiction = genre_consts[5]()
    
    lawyer = occupation_consts[5]()
    engineer = occupation_consts[3]()
    nurse = occupation_consts[2]()
    teacher = occupation_consts[4]()
    artist = occupation_consts[0]()
    doctor = occupation_consts[1]()
    
    # Clue 1: Alice is the person who loves fantasy books.
    s.add(Or([And(name_vars[i] == alice, genre_vars[i] == fantasy) for i in range(6)]))
    
    # Clue 2: The person who loves mystery books and Bob are next to each other.
    for i in range(6):
        adjacent = []
        if i > 0:
            adjacent.append(name_vars[i-1] == bob)
        if i < 5:
            adjacent.append(name_vars[i+1] == bob)
        s.add(Implies(genre_vars[i] == mystery, Or(adjacent)))
    
    # Clue 3: Carol is the person who loves mystery books.
    s.add(Or([And(name_vars[i] == carol, genre_vars[i] == mystery) for i in range(6)]))
    
    # Clue 4: The person who is a lawyer is the person who loves fantasy books.
    s.add(Or([And(occupation_vars[i] == lawyer, genre_vars[i] == fantasy) for i in range(6)]))
    
    # Clue 5: Bob is not in the fifth house.
    s.add(name_vars[4] != bob)
    
    # Clue 6: Arnold is somewhere to the left of the person who is an engineer.
    for i in range(6):
        for j in range(6):
            if i < j:
                s.add(Implies(And(name_vars[i] == arnold, occupation_vars[j] == engineer), True))
    
    # Clue 7: The person who is a nurse is directly left of Alice.
    for i in range(5):
        s.add(Implies(occupation_vars[i] == nurse, name_vars[i+1] == alice))
    
    # Clue 8: The person who loves biography books is the person who is a teacher.
    s.add(Or([And(genre_vars[i] == biography, occupation_vars[i] == teacher) for i in range(6)]))
    
    # Clue 9: The person who loves historical fiction books is somewhere to the left of the person who is a teacher.
    for i in range(6):
        for j in range(6):
            if i < j:
                s.add(Implies(And(genre_vars[i] == historical_fiction, occupation_vars[j] == teacher), True))
    
    # Clue 10: The person who is a doctor is in the first house.
    s.add(occupation_vars[0] == doctor)
    
    # Clue 11: The person who loves science fiction books is the person who is an artist.
    s.add(Or([And(genre_vars[i] == science_fiction, occupation_vars[i] == artist) for i in range(6)]))
    
    # Clue 12: Eric is in the third house.
    s.add(name_vars[2] == eric)
    
    # Clue 13: The person who loves mystery books is not in the fifth house.
    s.add(genre_vars[4] != mystery)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        
        # Prepare results
        rows = []
        for i in range(6):
            house_num = str(i+1)
            name_val = str(m.evaluate(name_vars[i]))
            genre_val = str(m.evaluate(genre_vars[i]))
            occupation_val = str(m.evaluate(occupation_vars[i]))
            rows.append([house_num, name_val, genre_val, occupation_val])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Occupation"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()