from z3 import *

def main():
    cities = ["Mykonos", "Dublin", "Krakow", "Istanbul", "Venice", "Naples", "Brussels", "Frankfurt"]
    n = len(cities)
    req_days = [4, 5, 4, 3, 3, 4, 2, 3]  # in the order of the cities list

    allowed_edges = [
        (0, 5), (1, 6), (3, 4), (2, 7), (1, 5), (2, 6), (3, 5), (5, 6), (3, 7), (6, 7), 
        (2, 3), (3, 6), (4, 7), (5, 7), (1, 2), (4, 6), (4, 5), (1, 3), (1, 4), (1, 7)
    ]

    # Create solver and variables
    s = Solver()
    
    # Sequence of cities (indexed 0 to 7)
    seq = [Int('seq_%d' % i) for i in range(n)]
    
    # Start and end days for each city
    start = [Int('start_%d' % i) for i in range(n)]
    end = [Int('end_%d' % i) for i in range(n)]
    
    # Fix the first city as Mykonos (index0)
    s.add(seq[0] == 0)
    
    # Sequence must be a permutation of cities
    s.add(Distinct(seq))
    for i in range(n):
        s.add(seq[i] >= 0, seq[i] < n)
    
    # Fixed constraints for Mykonos and Dublin
    s.add(start[0] == 1, end[0] == 4)
    s.add(start[1] == 11, end[1] == 15)
    
    # Duration constraints for each city
    for i in range(n):
        s.add(end[i] == start[i] + req_days[i] - 1)
    
    # Chain constraints: end of current city equals start of next city
    for i in range(n-1):
        curr_city = seq[i]
        next_city = seq[i+1]
        s.add(end[curr_city] == start[next_city])
    
    # Entire trip ends at day 21
    s.add(end[seq[n-1]] == 21)
    
    # Event constraints
    # Istanbul (index3) must have at least one day between 9 and 11
    s.add(start[3] <= 11, end[3] >= 9)
    # Frankfurt (index7) must have at least one day between 15 and 17
    s.add(start[7] <= 17, end[7] >= 15)
    
    # Flight connection constraints for consecutive cities
    for i in range(n-1):
        city_i = seq[i]
        city_j = seq[i+1]
        edge_constraints = []
        for edge in allowed_edges:
            edge_constraints.append(Or(
                And(city_i == edge[0], city_j == edge[1]),
                And(city_i == edge[1], city_j == edge[0])
            ))
        s.add(Or(edge_constraints))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        # Extract sequence
        seq_val = [m.evaluate(seq[i]).as_long() for i in range(n)]
        # Extract start and end days
        start_val = [m.evaluate(start[i]).as_long() for i in range(n)]
        end_val = [m.evaluate(end[i]).as_long() for i in range(n)]
        
        # Build itinerary
        itinerary = []
        for i in range(n):
            city_idx = seq_val[i]
            s_day = start_val[city_idx]
            e_day = end_val[city_idx]
            # Entire stay record
            if s_day == e_day:
                day_str = "Day %d" % s_day
            else:
                day_str = "Day %d-%d" % (s_day, e_day)
            itinerary.append({"day_range": day_str, "place": cities[city_idx]})
            # If not the last city, add departure and arrival records for the flight day
            if i < n-1:
                # Departure from current city
                itinerary.append({"day_range": "Day %d" % e_day, "place": cities[city_idx]})
                # Arrival at next city
                next_city_idx = seq_val[i+1]
                itinerary.append({"day_range": "Day %d" % e_day, "place": cities[next_city_idx]})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()