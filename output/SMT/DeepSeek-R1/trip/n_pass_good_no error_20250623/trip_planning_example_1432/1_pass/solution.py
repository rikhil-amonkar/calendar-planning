from z3 import *

def main():
    # Required days for each city: Frankfurt, Salzburg, Athens, Reykjavik, Bucharest, Valencia, Vienna, Amsterdam, Stockholm, Riga
    required_days = [4, 5, 5, 5, 3, 2, 5, 3, 3, 3]
    city_names = [
        "Frankfurt",
        "Salzburg",
        "Athens",
        "Reykjavik",
        "Bucharest",
        "Valencia",
        "Vienna",
        "Amsterdam",
        "Stockholm",
        "Riga"
    ]
    
    # Define the allowed flights (both bidirectional and directed)
    bidirectional_pairs = [
        (0,5), (5,0),
        (6,4), (4,6),
        (2,4), (4,2),
        (0,9), (9,0),
        (2,8), (8,2),
        (4,7), (7,4),
        (0,7), (7,0),
        (6,8), (8,6),
        (3,7), (7,3),
        (0,3), (3,0),
        (7,8), (8,7),
        (5,7), (7,5),
        (0,6), (6,0),
        (4,5), (5,4),
        (0,4), (4,0),
        (0,8), (8,0),
        (5,6), (6,5),
        (0,1), (1,0),
        (7,6), (6,7),
        (8,3), (3,8),
        (7,9), (9,7),
        (8,9), (9,8),
        (6,3), (3,6),
        (2,7), (7,2),
        (0,2), (2,0),
        (6,2), (2,6),
        (4,9), (9,4)
    ]
    directed_pairs = [
        (5,2),  # Valencia to Athens
        (2,9),  # Athens to Riga
        (3,2)   # Reykjavik to Athens
    ]
    allowed_flights = set(bidirectional_pairs) | set(directed_pairs)
    
    s = Solver()
    
    # End day variables for the first 10 stays: e1, e2, ..., e10
    e = [Int('e%d' % i) for i in range(1, 11)]
    # City assignment for the 11 stays
    city_vars = [Int('city%d' % i) for i in range(11)]
    
    # Constraints: 1 <= e1 <= e2 <= ... <= e10 <= 29
    for i in range(10):
        s.add(e[i] >= 1)
        s.add(e[i] <= 29)
    for i in range(9):
        s.add(e[i] <= e[i+1])
    
    # The entire list of end points: [1, e1, e2, ..., e10, 29]
    ends = [1] + e + [29]
    
    # Durations for each stay: duration[i] = (ends[i+1] - ends[i]) + 1
    durations = []
    for i in range(11):
        durations.append(ends[i+1] - ends[i] + 1)
    
    # Constraint: each city must be visited at least once
    for c in range(10):
        count_c = Sum([If(city_vars[i] == c, 1, 0) for i in range(11)])
        s.add(count_c >= 1)
    
    # Constraint: total days in each city must equal required_days
    for c in range(10):
        total_dur = 0
        for i in range(11):
            total_dur += If(city_vars[i] == c, durations[i], 0)
        s.add(total_dur == required_days[c])
    
    # Event constraints
    
    # Valencia (city5) must cover days 5 and 6
    for d in [5, 6]:
        in_city = False
        for i in range(11):
            # Check if stay i is in Valencia and covers day d
            cond = And(city_vars[i] == 5, ends[i] <= d, d <= ends[i+1])
            in_city = Or(in_city, cond)
        s.add(in_city)
    
    # Riga (city9) must cover days 18,19,20
    for d in [18,19,20]:
        in_city = False
        for i in range(11):
            cond = And(city_vars[i] == 9, ends[i] <= d, d <= ends[i+1])
            in_city = Or(in_city, cond)
        s.add(in_city)
    
    # Athens (city2) must cover days 14,15,16,17,18
    for d in [14,15,16,17,18]:
        in_city = False
        for i in range(11):
            cond = And(city_vars[i] == 2, ends[i] <= d, d <= ends[i+1])
            in_city = Or(in_city, cond)
        s.add(in_city)
    
    # Vienna (city6) must cover at least one day in [6,10]
    in_vienna = False
    for d in range(6, 11):  # d from 6 to 10 inclusive
        for i in range(11):
            cond = And(city_vars[i] == 6, ends[i] <= d, d <= ends[i+1])
            in_vienna = Or(in_vienna, cond)
    s.add(in_vienna)
    
    # Stockholm (city8) must cover at least one day in [1,3]
    in_stockholm = False
    for d in range(1, 4):  # d from 1 to 3 inclusive
        for i in range(11):
            cond = And(city_vars[i] == 8, ends[i] <= d, d <= ends[i+1])
            in_stockholm = Or(in_stockholm, cond)
    s.add(in_stockholm)
    
    # Flight constraints between consecutive stays
    for i in range(10):
        c1 = city_vars[i]
        c2 = city_vars[i+1]
        # The pair (c1, c2) must be in allowed_flights
        conds = []
        for flight in allowed_flights:
            conds.append(And(c1 == flight[0], c2 == flight[1]))
        s.add(Or(conds))
    
    if s.check() == sat:
        m = s.model()
        # Extract the end values
        e_vals = [m[var].as_long() for var in e]
        # The entire ends list: [1, e1, e2, ..., e10, 29]
        ends_vals = [1] + e_vals + [29]
        # Extract the city assignments
        city_vals = [m[var].as_long() for var in city_vars]
        
        # Build the itinerary
        itinerary = []
        for i in range(11):
            s_val = ends_vals[i]
            e_val = ends_vals[i+1]
            if s_val == e_val:
                day_range_str = "Day %d" % s_val
            else:
                day_range_str = "Day %d-%d" % (s_val, e_val)
            itinerary.append({"day_range": day_range_str, "place": city_names[city_vals[i]]})
            if i < 10:
                # Flight day: the last day of this stay (e_val) is the flight day
                itinerary.append({"day_range": "Day %d" % e_val, "place": city_names[city_vals[i]]})
                itinerary.append({"day_range": "Day %d" % e_val, "place": city_names[city_vals[i+1]]})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()