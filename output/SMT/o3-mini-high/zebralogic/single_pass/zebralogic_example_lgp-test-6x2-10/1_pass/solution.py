from z3 import *
import json

# Define integer variables for the houses (positions 1 to 6) for each person
Arnold = Int("Arnold")
Eric   = Int("Eric")
Peter  = Int("Peter")
Alice  = Int("Alice")
Carol  = Int("Carol")
Bob    = Int("Bob")

# Define integer variables for the houses for each music genre.
pop       = Int("pop")
jazz      = Int("jazz")
classical = Int("classical")
rock      = Int("rock")
hip_hop   = Int("hip_hop")
country   = Int("country")

s = Solver()

# Each person lives in a house numbered 1..6, and they are all in different houses.
persons = [Arnold, Eric, Peter, Alice, Carol, Bob]
for p in persons:
    s.add(And(p >= 1, p <= 6))
s.add(Distinct(Arnold, Eric, Peter, Alice, Carol, Bob))

# Each music genre is featured in one house, numbers 1..6, all distinct.
genres = [pop, jazz, classical, rock, hip_hop, country]
for g in genres:
    s.add(And(g >= 1, g <= 6))
s.add(Distinct(pop, jazz, classical, rock, hip_hop, country))

# Clue 1: Bob is directly left of the person who loves jazz.
s.add(jazz == Bob + 1)

# Clue 2: Eric is somewhere to the left of the person who loves hip-hop.
s.add(Eric < hip_hop)

# Clue 3: Carol is in the sixth house.
s.add(Carol == 6)

# Clue 4: Eric and the person who loves hip-hop music are next to each other.
s.add(Or(Eric == hip_hop + 1, Eric == hip_hop - 1))

# Clue 5: The person who loves country music is Carol.
s.add(country == Carol)

# Clue 6: Arnold is not in the fifth house.
s.add(Arnold != 5)

# Clue 7: Arnold is somewhere to the right of the person who loves pop music.
s.add(Arnold > pop)

# Clue 8: The person who loves pop music is Peter.
s.add(pop == Peter)

# Clue 9: The person who loves hip-hop music is in the third house.
s.add(hip_hop == 3)

# Clue 10: There is one house between Peter and Bob.
s.add(Or(Peter == Bob + 2, Bob == Peter + 2))

# Clue 11: The person who loves rock music is not in the fifth house.
s.add(rock != 5)

# Check if the constraints are satisfiable and extract the model.
if s.check() == sat:
    m = s.model()
    # Create a mapping from house number to person.
    house_person = {}
    for var, name in [(Arnold, "Arnold"), (Eric, "Eric"), (Peter, "Peter"),
                      (Alice, "Alice"), (Carol, "Carol"), (Bob, "Bob")]:
        house_person[m[var].as_long()] = name
        
    # Create a mapping from house number to music genre.
    # Note: while our variable is called hip_hop, the output should be "hip hop".
    house_music = {}
    for var, genre in [(pop, "pop"), (jazz, "jazz"), (classical, "classical"),
                       (rock, "rock"), (hip_hop, "hip hop"), (country, "country")]:
        house_music[m[var].as_long()] = genre

    # Assemble the solution rows in order from house 1 to 6.
    rows = []
    for h in range(1, 7):
        name = house_person[h]
        music = house_music[h]
        rows.append([str(h), name, music])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "MusicGenre"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")