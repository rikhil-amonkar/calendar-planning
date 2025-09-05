import json
from z3 import *

def main():
    # Define the enums for names and vacations
    NameSort, (Bob, Peter, Alice, Eric, Carol, Arnold) = EnumSort('Name', ['Bob', 'Peter', 'Alice', 'Eric', 'Carol', 'Arnold'])
    VacationSort, (mountain, camping, cruise, city, cultural, beach) = EnumSort('Vacation', ['mountain', 'camping', 'cruise', 'city', 'cultural', 'beach'])
    
    # Create arrays for names and vacations for each house (index 0 to 5 for houses 1 to 6)
    n = [Const(f'n_{i+1}', NameSort) for i in range(6)]
    v = [Const(f'v_{i+1}', VacationSort) for i in range(6)]
    
    s = Solver()
    
    # Each house has distinct name and vacation
    s.add(Distinct(n))
    s.add(Distinct(v))
    
    # Clue 3: Eric is in the second house.
    s.add(n[1] == Eric)
    
    # Clue 4: The person who goes on cultural tours is in the third house.
    s.add(v[2] == cultural)
    
    # Clue 7: The person who goes on cultural tours is Peter.
    s.add(n[2] == Peter)
    
    # Clue 9: The person who prefers city breaks is in the fourth house.
    s.add(v[3] == city)
    
    # Clue 6: The person who enjoys camping trips is not in the first house.
    s.add(v[0] != camping)
    
    # Clue 2: Eric is somewhere to the right of Alice.
    alice_house = Int('alice_house')
    s.add(Or([And(n[i] == Alice, alice_house == i+1) for i in range(6)]))
    s.add(alice_house < 2)  # Eric is in house 2
    
    # Clue 1: The person who goes on cultural tours is left of the person who loves beach vacations.
    beach_house = Int('beach_house')
    s.add(Or([And(v[i] == beach, beach_house == i+1) for i in range(6)]))
    s.add(3 < beach_house)  # cultural is in house 3
    
    # Clue 5: Bob is directly left of Arnold.
    bob_house = Int('bob_house')
    arnold_house = Int('arnold_house')
    s.add(Or([And(n[i] == Bob, bob_house == i+1) for i in range(6)]))
    s.add(Or([And(n[i] == Arnold, arnold_house == i+1) for i in range(6)]))
    s.add(arnold_house == bob_house + 1)
    
    # Clue 8: The person who likes going on cruises is Bob.
    for i in range(6):
        s.add(If(v[i] == cruise, n[i] == Bob, True))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        rows = []
        # Map Z3 enum values to their string names
        name_map = {Bob: "Bob", Peter: "Peter", Alice: "Alice", Eric: "Eric", Carol: "Carol", Arnold: "Arnold"}
        vacation_map = {mountain: "mountain", camping: "camping", cruise: "cruise", city: "city", cultural: "cultural", beach: "beach"}
        
        for i in range(6):
            name_val = m.eval(n[i])
            vacation_val = m.eval(v[i])
            # Use the maps to get string representations
            rows.append([str(i+1), name_map[name_val], vacation_map[vacation_val]])
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()