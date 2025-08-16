from z3 import *
import json

def solve_puzzle():
    # Create integer variables for the house positions (1 to 6) for each person.
    alice  = Int("alice")
    bob    = Int("bob")
    carol  = Int("carol")
    eric   = Int("eric")
    peter  = Int("peter")
    arnold = Int("arnold")
    
    # Create integer variables for the house positions (1 to 6) for each vacation type.
    # The vacations are: mountain, camping, cruise, city, cultural, beach.
    vac_mountain = Int("vac_mountain")
    vac_camping  = Int("vac_camping")
    vac_cruise   = Int("vac_cruise")
    vac_city     = Int("vac_city")
    vac_cultural = Int("vac_cultural")
    vac_beach    = Int("vac_beach")
    
    s = Solver()
    
    # Each person is assigned a house between 1 and 6.
    persons = [alice, bob, carol, eric, peter, arnold]
    for p in persons:
        s.add(p >= 1, p <= 6)
    s.add(Distinct(alice, bob, carol, eric, peter, arnold))
    
    # Each vacation is assigned a unique house number between 1 and 6.
    vacations = [vac_mountain, vac_camping, vac_cruise, vac_city, vac_cultural, vac_beach]
    for v in vacations:
        s.add(v >= 1, v <= 6)
    s.add(Distinct(vac_mountain, vac_camping, vac_cruise, vac_city, vac_cultural, vac_beach))
    
    # Clue 3: Eric is in the second house.
    s.add(eric == 2)
    
    # Clue 4: The person who goes on cultural tours is in the third house.
    s.add(vac_cultural == 3)
    
    # Clue 7: The person who goes on cultural tours is Peter.
    s.add(peter == vac_cultural)
    
    # Clue 9: The person who prefers city breaks is in the fourth house.
    s.add(vac_city == 4)
    
    # Clue 5: Bob is directly left of Arnold.
    s.add(bob + 1 == arnold)
    
    # Clue 8: The person who likes going on cruises is Bob.
    s.add(bob == vac_cruise)
    
    # Clue 6: The person who enjoys camping trips is not in the first house.
    s.add(vac_camping != 1)
    
    # Clue 1: The person who goes on cultural tours is somewhere to the left of the person who loves beach vacations.
    s.add(vac_cultural < vac_beach)
    
    # Clue 2: Eric is somewhere to the right of Alice.
    s.add(eric > alice)
    
    # Solve the constraints.
    if s.check() == sat:
        m = s.model()
        
        # Build a mapping from house number to the person's name.
        house_to_name = {}
        house_to_name[m.evaluate(alice).as_long()]  = "Alice"
        house_to_name[m.evaluate(bob).as_long()]    = "Bob"
        house_to_name[m.evaluate(carol).as_long()]  = "Carol"
        house_to_name[m.evaluate(eric).as_long()]   = "Eric"
        house_to_name[m.evaluate(peter).as_long()]  = "Peter"
        house_to_name[m.evaluate(arnold).as_long()] = "Arnold"
        
        # Build a mapping from house number to the vacation type.
        house_to_vacation = {}
        house_to_vacation[m.evaluate(vac_mountain).as_long()] = "mountain"
        house_to_vacation[m.evaluate(vac_camping).as_long()]  = "camping"
        house_to_vacation[m.evaluate(vac_cruise).as_long()]   = "cruise"
        house_to_vacation[m.evaluate(vac_city).as_long()]     = "city"
        house_to_vacation[m.evaluate(vac_cultural).as_long()] = "cultural"
        house_to_vacation[m.evaluate(vac_beach).as_long()]    = "beach"
        
        # Prepare the output rows in order from house 1 to house 6.
        rows = []
        for house in range(1, 7):
            rows.append([str(house), house_to_name[house], house_to_vacation[house]])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    solve_puzzle()