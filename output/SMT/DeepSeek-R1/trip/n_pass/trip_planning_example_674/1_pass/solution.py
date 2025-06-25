from z3 import *

def main():
    # City mapping and durations
    cities = ['Helsinki', 'Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']
    dur_list = [2, 3, 4, 4, 2, 4]  # Corresponding durations
    
    # Allowed directed flights (bidirectional and Reykjavik->Madrid)
    edges_int = [
        (0,4), (4,0),  # Helsinki-Reykjavik
        (5,1), (1,5),  # Budapest-Warsaw
        (2,3), (3,2),  # Madrid-Split
        (0,3), (3,0),  # Helsinki-Split
        (0,2), (2,0),  # Helsinki-Madrid
        (0,5), (5,0),  # Helsinki-Budapest
        (4,1), (1,4),  # Reykjavik-Warsaw
        (0,1), (1,0),  # Helsinki-Warsaw
        (2,5), (5,2),  # Madrid-Budapest
        (5,4), (4,5),  # Budapest-Reykjavik
        (2,1), (1,2),  # Madrid-Warsaw
        (1,3), (3,1),  # Warsaw-Split
        (4,2)          # Reykjavik->Madrid
    ]
    
    # Z3 variables for the sequence of cities
    seq = [Int(f'seq_{i}') for i in range(6)]
    s = Solver()
    
    # Each seq[i] must be between 0 and 5
    for i in range(6):
        s.add(seq[i] >= 0, seq[i] < 6)
    
    # Distinct cities in the sequence
    s.add(Distinct(seq))
    
    # Flight constraints between consecutive cities
    for i in range(5):
        s.add(Or([And(seq[i] == a, seq[i+1] == b) for (a, b) in edges_int]))
    
    # Duration lookup function
    def get_dur(city_code):
        return If(city_code == 0, 2,
               If(city_code == 1, 3,
               If(city_code == 2, 4,
               If(city_code == 3, 4,
               If(city_code == 4, 2, 4)))))  # 5 is Budapest
    
    # Cumulative durations
    cum = [0] * 7
    cum[0] = 0
    for j in range(6):
        cum[j+1] = cum[j] + get_dur(seq[j])
    
    # Helsinki must be first or second, and if second, first must be Reykjavik
    s.add(Or(
        seq[0] == 0,
        And(seq[1] == 0, seq[0] == 4)
    ))
    
    # Reykjavik and Warsaw constraints
    for k in range(6):
        start_day = 1 + cum[k] - k
        # Reykjavik (city4) must start on day 7, 8, or 9
        s.add(If(seq[k] == 4, Or(start_day == 7, start_day == 8, start_day == 9), True))
        # Warsaw (city1) must start between day 7 and 11 inclusive
        s.add(If(seq[k] == 1, And(start_day >= 7, start_day <= 11), True))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        seq_val = [m.evaluate(seq[i]).as_long() for i in range(6)]
        
        # Compute concrete start and end days
        cum_val = [0] * 7
        for j in range(6):
            cum_val[j+1] = cum_val[j] + dur_list[seq_val[j]]
        
        starts = []
        ends = []
        for k in range(6):
            start_day = 1 + cum_val[k] - k
            end_day = start_day + dur_list[seq_val[k]] - 1
            starts.append(start_day)
            ends.append(end_day)
        
        # Build itinerary
        itinerary = []
        for k in range(6):
            city_name = cities[seq_val[k]]
            start = starts[k]
            end = ends[k]
            itinerary.append({
                "day_range": f"Day {start}-{end}" if start != end else f"Day {start}",
                "place": city_name
            })
            if k < 5:
                itinerary.append({
                    "day_range": f"Day {end}",
                    "place": city_name
                })
                next_city = cities[seq_val[k+1]]
                itinerary.append({
                    "day_range": f"Day {end}",
                    "place": next_city
                })
        
        # Output result
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()