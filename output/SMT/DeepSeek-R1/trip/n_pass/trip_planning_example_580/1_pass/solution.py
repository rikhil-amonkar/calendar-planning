from z3 import *

def main():
    # Define city indices and names
    cities = ["Geneva", "Paris", "Porto", "Reykjavik", "Oslo"]
    req = [7, 6, 7, 2, 5]  # Required days per city

    # Direct flights as tuples (from_index, to-index)
    direct_flights = [
        (0, 1), (1, 0),
        (0, 2), (2, 0),
        (0, 4), (4, 0),
        (1, 2), (2, 1),
        (1, 3), (3, 1),
        (1, 4), (4, 1),
        (2, 4), (4, 2),
        (3, 4), (4, 3)
    ]

    # Create solver
    s = Solver()

    # Sequence of cities: 5 elements, first is Geneva (0), last is Oslo (4)
    seq = [Int(f'seq_{i}') for i in range(5)]
    s.add(seq[0] == 0)  # Start with Geneva
    s.add(seq[4] == 4)  # End with Oslo

    # Middle three cities are distinct and in {1,2,3}
    for i in range(1, 4):
        s.add(seq[i] >= 1, seq[i] <= 3)
    s.add(Distinct(seq[1], seq[2], seq[3]))

    # Start and end days for each city
    start = [Int(f'start_{i}') for i in range(5)]
    end = [Int(f'end_{i}') for i in range(5)]

    # Fixed start and end for Geneva and Oslo
    s.add(start[0] == 1)   # Geneva starts on day 1
    s.add(end[0] == 7)     # Geneva ends on day 7
    s.add(start[4] == 19)  # Oslo starts on day 19
    s.add(end[4] == 23)    # Oslo ends on day 23

    # Consecutive city constraints: end of current city = start of next
    for i in range(4):
        s.add(end[seq[i]] == start[seq[i+1]])

    # Direct flight constraints between consecutive cities
    for i in range(4):
        s.add(Or([And(seq[i] == u, seq[i+1] == v) for (u, v) in direct_flights]))

    # Stay duration constraints
    for i in range(5):
        length = end[i] - start[i] + 1
        s.add(length == req[i])
        s.add(start[i] >= 1, end[i] <= 23, start[i] <= end[i])

    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        seq_order = [m.evaluate(seq[i]).as_long() for i in range(5)]
        start_vals = [m.evaluate(start[i]).as_long() for i in range(5)]
        end_vals = [m.evaluate(end[i]).as_long() for i in range(5)]
        
        itinerary = []
        for i in range(5):
            city_index = seq_order[i]
            city_name = cities[city_index]
            s_val = start_vals[city_index]
            e_val = end_vals[city_index]
            
            if i > 0:
                itinerary.append({'day_range': f"Day {s_val}", 'place': city_name})
            
            itinerary.append({'day_range': f"Day {s_val}-{e_val}", 'place': city_name})
            
            if i < 4:
                itinerary.append({'day_range': f"Day {e_val}", 'place': city_name})
        
        result = {'itinerary': itinerary}
        print(f"{result}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()