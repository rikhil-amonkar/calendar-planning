from z3 import *

def main():
    # City index mapping
    city_index = {
        'Valencia': 0,
        'Oslo': 1,
        'Lyon': 2,
        'Prague': 3,
        'Paris': 4,
        'Nice': 5,
        'Seville': 6,
        'Tallinn': 7,
        'Mykonos': 8,
        'Lisbon': 9
    }
    
    index_to_city = {v: k for k, v in city_index.items()}
    
    # Durations for each city (by index)
    durations = [
        2,  # Valencia
        3,  # Oslo
        4,  # Lyon
        3,  # Prague
        4,  # Paris
        4,  # Nice
        5,  # Seville
        2,  # Tallinn
        5,  # Mykonos
        2   # Lisbon
    ]
    
    # Fixed start days
    fixed_starts = {
        city_index['Seville']: 5,
        city_index['Mykonos']: 21
    }
    
    # Build the graph of direct flights
    flight_strings = [
        "Lisbon and Paris",
        "Lyon and Nice",
        "Tallinn and Oslo",
        "Prague and Lyon",
        "Paris and Oslo",
        "Lisbon and Seville",
        "Prague and Lisbon",
        "Oslo and Nice",
        "Valencia and Paris",
        "Valencia and Lisbon",
        "Paris and Nice",
        "Nice and Mykonos",
        "Paris and Lyon",
        "Valencia and Lyon",
        "Prague and Oslo",
        "Prague and Paris",
        "Seville and Paris",
        "Oslo and Lyon",
        "Prague and Valencia",
        "Lisbon and Nice",
        "Lisbon and Oslo",
        "Valencia and Seville",
        "Lisbon and Lyon",
        "Paris and Tallinn",
        "Prague and Tallinn"
    ]
    
    neighbors = [[] for _ in range(10)]
    for flight in flight_strings:
        parts = flight.split(' and ')
        c1 = parts[0].strip()
        c2 = parts[1].strip()
        idx1 = city_index[c1]
        idx2 = city_index[c2]
        neighbors[idx1].append(idx2)
        neighbors[idx2].append(idx1)
    
    # Create Z3 solver and variables
    solver = Solver()
    
    # Sequence of cities: seq[0] is first, seq[9] is last
    seq = [Int('seq_%d' % i) for i in range(10)]
    # Start day for each city (by city index)
    s = [Int('s_%d' % i) for i in range(10)]
    
    # Constraints: each element in seq is between 0 and 9
    for i in range(10):
        solver.add(seq[i] >= 0, seq[i] < 10)
    
    # The sequence must be distinct
    solver.add(Distinct(seq))
    
    # Start day of first city is 1
    solver.add(s[seq[0]] == 1)
    
    # Chain constraint: start day of next city = start day of previous + duration of previous - 1
    for i in range(1, 10):
        solver.add(s[seq[i]] == s[seq[i-1]] + durations[seq[i-1]] - 1)
    
    # Fixed start days
    for idx, start_day in fixed_starts.items():
        solver.add(s[idx] == start_day)
    
    # Constraints for Valencia and Oslo
    # Valencia (index0): start day between 2 and 4
    solver.add(s[0] >= 2, s[0] <= 4)
    # Oslo (index1): start day between 11 and 15
    solver.add(s[1] >= 11, s[1] <= 15)
    
    # Flight connections: for each consecutive pair in the sequence, they must be connected by a direct flight
    for k in range(9):
        cond = False
        for i in range(10):
            # If current city is i, then next city must be in neighbors[i]
            next_in_neighbors = Or([seq[k+1] == j for j in neighbors[i]])
            cond = Or(cond, And(seq[k] == i, next_in_neighbors))
        solver.add(cond)
    
    # Check and get the model
    if solver.check() == sat:
        model = solver.model()
        seq_val = [model.evaluate(seq[i]).as_long() for i in range(10)]
        s_val = [model.evaluate(s[i]).as_long() for i in range(10)]
        
        def format_day(day):
            return f"Day {day}"
        
        def format_day_range(start, end):
            if start == end:
                return f"Day {start}"
            else:
                return f"Day {start}-{end}"
        
        itinerary = []
        for i in range(10):
            city_idx = seq_val[i]
            city_name = index_to_city[city_idx]
            start_day = s_val[city_idx]
            end_day = start_day + durations[city_idx] - 1
            
            itinerary.append({
                "day_range": format_day_range(start_day, end_day),
                "place": city_name
            })
            
            if i < 9:
                itinerary.append({
                    "day_range": format_day(end_day),
                    "place": city_name
                })
                next_city_idx = seq_val[i+1]
                next_city_name = index_to_city[next_city_idx]
                itinerary.append({
                    "day_range": format_day(end_day),
                    "place": next_city_name
                })
        
        output = {"itinerary": itinerary}
        print(output)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()