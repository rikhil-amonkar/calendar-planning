from z3 import *

def main():
    # Define cities and their durations
    cities = ["Venice", "Barcelona", "Copenhagen", "Lyon", "Reykjavik", "Dubrovnik", "Athens", "Tallinn", "Munich"]
    durs = [4, 3, 4, 4, 4, 5, 2, 5, 3]
    n = len(cities)
    
    # Flight list
    flight_list = [
        ('Copenhagen', 'Athens'),
        ('Copenhagen', 'Dubrovnik'),
        ('Munich', 'Tallinn'),
        ('Copenhagen', 'Munich'),
        ('Venice', 'Munich'),
        ('Reykjavik', 'Athens'),
        ('Athens', 'Dubrovnik'),
        ('Venice', 'Athens'),
        ('Lyon', 'Barcelona'),
        ('Copenhagen', 'Reykjavik'),
        ('Reykjavik', 'Munich'),
        ('Athens', 'Munich'),
        ('Lyon', 'Munich'),
        ('Barcelona', 'Reykjavik'),
        ('Venice', 'Copenhagen'),
        ('Barcelona', 'Dubrovnik'),
        ('Lyon', 'Venice'),
        ('Dubrovnik', 'Munich'),
        ('Barcelona', 'Athens'),
        ('Copenhagen', 'Barcelona'),
        ('Venice', 'Barcelona'),
        ('Barcelona', 'Munich'),
        ('Barcelona', 'Tallinn'),
        ('Copenhagen', 'Tallinn')
    ]
    
    # Build allowed matrix (0/1) for flights between cities
    allowed = [[0]*n for _ in range(n)]
    for city1, city2 in flight_list:
        try:
            idx1 = cities.index(city1)
            idx2 = cities.index(city2)
            allowed[idx1][idx2] = 1
            allowed[idx2][idx1] = 1
        except:
            pass  # Ignore if city not found
    
    # Collect allowed pairs (j, k) for which there is a flight
    allowed_pairs = []
    for j in range(n):
        for k in range(n):
            if allowed[j][k] == 1:
                allowed_pairs.append((j, k))
    
    # Create Z3 solver and variables
    s = Solver()
    
    # Assignment matrix: assign[i][j] is True if city j is at position i
    assign = [[Bool('a_%d_%d' % (i, j)) for j in range(n)] for i in range(n)]
    
    # Constraints: each position has exactly one city, each city is in exactly one position
    for i in range(n):
        s.add(Or([assign[i][j] for j in range(n)]))
        s.add(Sum([If(assign[i][j], 1, 0) for j in range(n)]) == 1)
    
    for j in range(n):
        s.add(Sum([If(assign[i][j], 1, 0) for i in range(n)]) == 1)
    
    # Prefix array: prefix[i] is the sum of (durs[j]-1) for cities before position i
    prefix = [Int('prefix_%d' % i) for i in range(n)]
    s.add(prefix[0] == 0)
    for i in range(1, n):
        # Sum of durs[j] * assign[i-1][j] for all j
        sum_dur = Sum([If(assign[i-1][j], durs[j], 0) for j in range(n)])
        s.add(prefix[i] == prefix[i-1] + sum_dur - 1)
    
    # Constraints for Barcelona (index 1), Copenhagen (index 2), Dubrovnik (index 5)
    # Barcelona: must be present between day 10 and 12 -> 8 <= S[1] <= 12
    # S[1] = 1 + sum_i (assign[i][1] * prefix[i])
    S_bcn = Int('S_bcn')
    s.add(S_bcn == 1 + Sum([If(assign[i][1], prefix[i], 0) for i in range(n)]))
    E_bcn = S_bcn + durs[1] - 1
    s.add(S_bcn <= 12)
    s.add(E_bcn >= 10)
    
    # Copenhagen: index 2
    S_cop = Int('S_cop')
    s.add(S_cop == 1 + Sum([If(assign[i][2], prefix[i], 0) for i in range(n)]))
    E_cop = S_cop + durs[2] - 1
    s.add(S_cop <= 10)
    s.add(E_cop >= 7)
    
    # Dubrovnik: index 5
    S_dub = Int('S_dub')
    s.add(S_dub == 1 + Sum([If(assign[i][5], prefix[i], 0) for i in range(n)]))
    E_dub = S_dub + durs[5] - 1
    s.add(S_dub <= 20)
    s.add(E_dub >= 16)
    
    # Flight constraints for consecutive positions
    for i in range(n-1):
        or_terms = []
        for j, k in allowed_pairs:
            or_terms.append(And(assign[i][j], assign[i+1][k]))
        s.add(Or(or_terms))
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        # Build the itinerary
        itinerary = []
        # For each position, determine the city and its start/end days
        for i in range(n):
            # Find the city at position i
            j_index = None
            for j in range(n):
                if model.evaluate(assign[i][j]):
                    j_index = j
                    break
            if j_index is None:
                continue
            city_name = cities[j_index]
            # Get prefix value for position i
            prefix_val = model.evaluate(prefix[i])
            if isinstance(prefix_val, IntNumRef):
                prefix_val = prefix_val.as_long()
            start = prefix_val + 1
            duration = durs[j_index]
            end = start + duration - 1
            # Format day range for the entire block
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": city_name})
            # If not the last city, add departure and arrival for the next city
            if i < n-1:
                # Departure from current city on day 'end'
                itinerary.append({"day_range": f"Day {end}", "place": city_name})
                # Find the next city
                j_next = None
                for j in range(n):
                    if model.evaluate(assign[i+1][j]):
                        j_next = j
                        break
                if j_next is not None:
                    next_city = cities[j_next]
                    itinerary.append({"day_range": f"Day {end}", "place": next_city})
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()