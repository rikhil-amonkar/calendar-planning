import json
from z3 import *

def main():
    # Define the attributes
    names = ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric']
    genres = ['romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction']
    occupations = ['artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer']
    
    # Create Z3 enums
    Name = Enum('Name', names)
    Genre = Enum('Genre', genres)
    Occupation = Enum('Occupation', occupations)
    
    # Create variables for each house
    houses = [1, 2, 3, 4, 5, 6]
    name_vars = [Const(f"name_{i}", Name) for i in houses]
    genre_vars = [Const(f"genre_{i}", Genre) for i in houses]
    occupation_vars = [Const(f"occupation_{i}", Occupation) for i in houses]
    
    s = Solver()
    
    # Each attribute must be unique (permutation)
    s.add(Distinct(name_vars))
    s.add(Distinct(genre_vars))
    s.add(Distinct(occupation_vars))
    
    # Extract specific values for constraints
    alice = Name.Alice
    bob = Name.Bob
    carol = Name.Carol
    eric = Name.Eric
    arnold = Name.Arnold
    
    fantasy = Genre.fantasy
    mystery = Genre.mystery
    biography = Genre.biography
    historical_fiction = Genre.historical_fiction
    science_fiction = Genre.science_fiction
    
    lawyer = Occupation.lawyer
    engineer = Occupation.engineer
    nurse = Occupation.nurse
    teacher = Occupation.teacher
    artist = Occupation.artist
    doctor = Occupation.doctor
    
    # Clue 1: Alice is the person who loves fantasy books.
    s.add(Exists([i], And(i >= 1, i <= 6, name_vars[i-1] == alice, genre_vars[i-1] == fantasy)))
    
    # Clue 2: The person who loves mystery books and Bob are next to each other.
    for i in range(1, 6):
        s.add(Implies(genre_vars[i-1] == mystery, Or(name_vars[i] == bob, name_vars[i-1] == bob)))
        s.add(Implies(genre_vars[i] == mystery, Or(name_vars[i-1] == bob, name_vars[i] == bob)))
    
    # Clue 3: Carol is the person who loves mystery books.
    s.add(Exists([i], And(i >= 1, i <= 6, name_vars[i-1] == carol, genre_vars[i-1] == mystery)))
    
    # Clue 4: The person who is a lawyer is the person who loves fantasy books.
    s.add(Exists([i], And(i >= 1, i <= 6, occupation_vars[i-1] == lawyer, genre_vars[i-1] == fantasy)))
    
    # Clue 5: Bob is not in the fifth house.
    s.add(name_vars[4] != bob)
    
    # Clue 6: Arnold is somewhere to the left of the person who is an engineer.
    for i in range(1, 6):
        for j in range(i+1, 7):
            s.add(Implies(And(name_vars[i-1] == arnold, occupation_vars[j-1] == engineer), i < j))
    
    # Clue 7: The person who is a nurse is directly left of Alice.
    for i in range(1, 6):
        s.add(Implies(And(occupation_vars[i-1] == nurse, name_vars[i] == alice), True))
    
    # Clue 8: The person who loves biography books is the person who is a teacher.
    s.add(Exists([i], And(i >= 1, i <= 6, genre_vars[i-1] == biography, occupation_vars[i-1] == teacher)))
    
    # Clue 9: The person who loves historical fiction books is somewhere to the left of the person who is a teacher.
    for i in range(1, 6):
        for j in range(i+1, 7):
            s.add(Implies(And(genre_vars[i-1] == historical_fiction, occupation_vars[j-1] == teacher), i < j))
    
    # Clue 10: The person who is a doctor is in the first house.
    s.add(occupation_vars[0] == doctor)
    
    # Clue 11: The person who loves science fiction books is the person who is an artist.
    s.add(Exists([i], And(i >= 1, i <= 6, genre_vars[i-1] == science_fiction, occupation_vars[i-1] == artist)))
    
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