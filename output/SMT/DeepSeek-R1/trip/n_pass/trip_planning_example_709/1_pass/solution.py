import json
from z3 import *

def main():
    # Define city indices and names
    cities = [0, 1, 2, 3, 4, 5]
    city_names = {
        0: "Helsinki",
        1: "Valencia",
        2: "Dubrovnik",
        3: "Porto",
        4: "Prague",
        5: "Reykjavik"
    }
    days_required = [4, 5, 4, 3, 3, 4]  # Helsinki, Valencia, Dubrovnik, Porto, Prague, Reykjavik
    
    # Allowed flight connections (symmetric)
    allowed_edges = [
        (0, 4), (4, 0),  # Helsinki <-> Prague
        (4, 1), (1, 4),  # Prague <-> Valencia
        (1, 3), (3, 1),  # Valencia <-> Porto
        (0, 5), (5, 0),  # Helsinki <-> Reykjavik
        (2, 0), (0, 2),  # Dubrovnik <-> Helsinki
        (5, 4), (4, 5)   # Reykjavik <-> Prague
    ]
    
    # Create Z3 solver
    solver = Solver()
    
    # Sequence variables: seq[0] to seq[5] represent the order of cities
    seq = [Int(f'seq_{i}') for i in range(6)]
    
    # Start and end day variables for each city (by city index)
    s = [Int(f's_{i}') for i in range(6)]
    e = [Int(f'e_{i}') for i in range(6)]
    
    # Constraints: each seq variable is between 0 and 5 and all are distinct
    solver.add([And(seq_i >= 0, seq_i <= 5) for seq_i in seq])
    solver.add(Distinct(seq))
    
    # Duration constraints: e[i] = s[i] + (days_required[i] - 1)
    for i in range(6):
        solver.add(e[i] == s[i] + days_required[i] - 1)
    
    # First city starts on day 1, last city ends on day 18
    solver.add(s[seq[0]] == 1)
    solver.add(e[seq[5]] == 18)
    
    # Consecutive cities: end day of current equals start day of next
    for i in range(5):
        solver.add(e[seq[i]] == s[seq[i+1]])
    
    # Flight connections: consecutive cities must have a direct flight
    for i in range(5):
        a = seq[i]
        b = seq[i+1]
        edge_constraints = []
        for edge in allowed_edges:
            edge_constraints.append(And(a == edge[0], b == edge[1]))
        solver.add(Or(edge_constraints))
    
    # Porto constraint: start day between 14 and 16 (inclusive)
    porto_index = 3
    solver.add(s[porto_index] >= 14)
    solver.add(s[porto_index] <= 16)
    
    # All start and end days between 1 and 18
    for i in range(6):
        solver.add(s[i] >= 1)
        solver.add(s[i] <= 18)
        solver.add(e[i] >= 1)
        solver.add(e[i] <= 18)
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        # Extract sequence as integers
        seq_val = [model.evaluate(seq_i).as_long() for seq_i in seq]
        # Extract start and end days for each city
        s_val = [model.evaluate(s_i).as_long() for s_i in s]
        e_val = [model.evaluate(e_i).as_long() for e_i in e]
        
        # Build itinerary
        itinerary = []
        
        # First city in sequence
        first_city = seq_val[0]
        s0 = s_val[first_city]
        e0 = e_val[first_city]
        itinerary.append({"day_range": f"Day {s0}-{e0}", "place": city_names[first_city]})
        itinerary.append({"day_range": f"Day {e0}", "place": city_names[first_city]})  # Departure
        
        # Middle cities (positions 1 to 4 in sequence)
        for i in range(1, 5):
            city_idx = seq_val[i]
            sc = s_val[city_idx]
            ec = e_val[city_idx]
            itinerary.append({"day_range": f"Day {sc}", "place": city_names[city_idx]})  # Arrival
            itinerary.append({"day_range": f"Day {sc}-{ec}", "place": city_names[city_idx]})
            itinerary.append({"day_range": f"Day {ec}", "place": city_names[city_idx]})  # Departure
        
        # Last city in sequence
        last_city = seq_val[5]
        s_last = s_val[last_city]
        e_last = e_val[last_city]
        itinerary.append({"day_range": f"Day {s_last}", "place": city_names[last_city]})  # Arrival
        itinerary.append({"day_range": f"Day {s_last}-{e_last}", "place": city_names[last_city]})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()