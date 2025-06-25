from z3 import *

def main():
    # Cities and their indices
    cities = ["Geneva", "Munich", "Bucharest", "Valencia", "Stuttgart"]
    # Index mapping: Geneva:0, Munich:1, Bucharest:2, Valencia:3, Stuttgart:4
    
    # Create solver
    s = Solver()
    
    # Sequence of cities (order of visit)
    seq = [Int('seq0'), Int('seq1'), Int('seq2'), Int('seq3'), Int('seq4')]
    
    # Start and end days for each city
    start = [Int(f'start_{i}') for i in range(5)]
    end = [Int(f'end_{i}') for i in range(5)]
    
    # Constraints for sequence: must be distinct and within [0,4]
    s.add(Distinct(seq))
    for i in range(5):
        s.add(seq[i] >= 0)
        s.add(seq[i] < 5)
    
    # First city must be Geneva (index 0)
    s.add(seq[0] == 0)
    
    # Geneva: start on day 1, duration 4 days -> end on day 4
    s.add(start[0] == 1)
    s.add(end[0] == 4)  # 1 + 3 = 4
    
    # For the sequence: the start of next city = end of previous
    for i in range(1, 5):
        s.add(start[seq[i]] == end[seq[i-1]])
    
    # Last city ends on day 17
    s.add(end[seq[4]] == 17)
    
    # Durations for other cities
    # Munich: 7 days -> end = start + 6
    s.add(end[1] == start[1] + 6)
    # Bucharest: 2 days -> end = start + 1
    s.add(end[2] == start[2] + 1)
    # Valencia: 6 days -> end = start + 5
    s.add(end[3] == start[3] + 5)
    # Stuttgart: 2 days -> end = start + 1
    s.add(end[4] == start[4] + 1)
    
    # Munich must be the second city (since it starts at day 4, immediately after Geneva)
    s.add(seq[1] == 1)
    
    # Direct flight constraints: allowed pairs (undirected)
    allowed_pairs = [
        (0, 1), (1, 0),
        (1, 3), (3, 1),
        (2, 3), (3, 2),
        (1, 2), (2, 1),
        (3, 4), (4, 3),
        (0, 3), (3, 0)
    ]
    
    # Consecutive cities in the sequence must have direct flights
    for i in range(4):
        c1 = seq[i]
        c2 = seq[i+1]
        constraints = []
        for a, b in allowed_pairs:
            constraints.append(And(c1 == a, c2 == b))
        s.add(Or(constraints))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        seq_val = [m.evaluate(seq[i]).as_long() for i in range(5)]
        start_val = [m.evaluate(start[i]).as_long() for i in range(5)]
        end_val = [m.evaluate(end[i]).as_long() for i in range(5)]
        
        # Map indices to city names
        seq_cities = [cities[idx] for idx in seq_val]
        itinerary = []
        
        for i in range(5):
            city = seq_cities[i]
            s_start = start_val[seq_val[i]]
            s_end = end_val[seq_val[i]]
            
            # Entire stay block
            if s_start == s_end:
                day_range = f"Day {s_start}"
            else:
                day_range = f"Day {s_start}-{s_end}"
            itinerary.append({"day_range": day_range, "place": city})
            
            # If not the last city, add flight day entries
            if i < 4:
                # Departure from current city
                itinerary.append({"day_range": f"Day {s_end}", "place": city})
                # Arrival in next city
                next_city = seq_cities[i+1]
                itinerary.append({"day_range": f"Day {s_end}", "place": next_city})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()