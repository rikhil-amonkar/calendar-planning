from z3 import *
import json

def main():
    # City indices and names
    cities = ['Stockholm', 'Hamburg', 'Florence', 'Istanbul', 'Oslo', 'Vilnius', 'Santorini', 'Munich', 'Frankfurt', 'Krakow']
    city_dict = {i: name for i, name in enumerate(cities)}
    
    # Durations for each city: [0:Stockholm, 1:Hamburg, ...]
    durations_arr = [3, 5, 2, 5, 5, 5, 2, 5, 4, 5]
    
    # Directed flight edges: (from, to)
    allowed_edges = [
        (0,4), (4,0),   # Oslo and Stockholm
        (9,8), (8,9),   # Krakow and Frankfurt
        (9,3), (3,9),   # Krakow and Istanbul
        (7,0), (0,7),   # Munich and Stockholm
        (1,0), (0,1),   # Hamburg and Stockholm
        (4,3), (3,4),   # Oslo and Istanbul
        (3,0), (0,3),   # Istanbul and Stockholm
        (4,9), (9,4),   # Oslo and Krakow
        (5,3), (3,5),   # Vilnius and Istanbul
        (4,5), (5,4),   # Oslo and Vilnius
        (8,3), (3,8),   # Frankfurt and Istanbul
        (4,8), (8,4),   # Oslo and Frankfurt
        (7,1), (1,7),   # Munich and Hamburg
        (7,3), (3,7),   # Munich and Istanbul
        (4,7), (7,4),   # Oslo and Munich
        (8,2), (2,8),   # Frankfurt and Florence
        (4,1), (1,4),   # Oslo and Hamburg
        (5,8), (8,5),   # Vilnius and Frankfurt
        (9,7), (7,9),   # Krakow and Munich
        (1,3), (3,1),   # Hamburg and Istanbul
        (8,0), (0,8),   # Frankfurt and Stockholm
        (8,7), (7,8),   # Frankfurt and Munich
        (9,0), (0,9),   # Krakow and Stockholm
        # Directed edges
        (9,5),           # from Krakow to Vilnius
        (2,7),           # from Florence to Munich
        (0,6),           # from Stockholm to Santorini
        (6,4),           # from Santorini to Oslo
        (5,7)            # from Vilnius to Munich
    ]
    
    # Create Z3 solver
    s = Solver()
    
    # Sequence of cities (10 elements)
    c = [Int('c_%d' % i) for i in range(10)]
    
    # Each city in the sequence is between 0 and 9
    for i in range(10):
        s.add(c[i] >= 0, c[i] <= 9)
    
    # All cities distinct
    s.add(Distinct(c))
    
    # Durations for each city in the sequence
    dur_seq = [Int('d_%d' % i) for i in range(10)]
    for i in range(10):
        s.add(dur_seq[i] == durations_arr[c[i]])
    
    # Cumulative sums S: S[i] = sum_{j=0}^{i} (dur_seq[j] - 1)
    S = [Int('S_%d' % i) for i in range(10)]
    s.add(S[0] == dur_seq[0] - 1)
    for i in range(1, 10):
        s.add(S[i] == S[i-1] + (dur_seq[i] - 1))
    
    # k: index of Krakow (city 9)
    k = Int('k')
    s.add(k >= 0, k < 10)
    # l: index of Istanbul (city 3)
    l_var = Int('l')
    s.add(l_var >= 0, l_var < 10)
    
    # Constraints for k and l_var
    # Krakow must be in the sequence at position k
    s.add(Or([And(c[i] == 9, k == i) for i in range(10)]))
    # Istanbul must be in the sequence at position l_var
    s.add(Or([And(c[i] == 3, l_var == i) for i in range(10)]))
    
    # k and l_var must be at least 1 (since cumulative sums before them are defined and must be 4 and 24, respectively)
    s.add(k > 0, l_var > 0)
    s.add(k < l_var)
    
    # Constraints on cumulative sums
    # Before Krakow: S[k-1] == 4
    s.add(S[k-1] == 4)
    # Before Istanbul: S[l_var-1] == 24
    s.add(S[l_var-1] == 24)
    
    # Flight connections: for each consecutive pair (c[i], c[i+1]), (c[i], c[i+1]) must be in allowed_edges
    for i in range(9):
        constraints = []
        for edge in allowed_edges:
            u, v = edge
            constraints.append(And(c[i] == u, c[i+1] == v))
        s.add(Or(constraints))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        # Extract the sequence
        seq = [model.evaluate(c[i]).as_long() for i in range(10)]
        # Extract k and l_var to compute arrival and departure days
        k_val = model.evaluate(k).as_long()
        l_val = model.evaluate(l_var).as_long()
        
        # Compute arrival and departure days
        a = [0] * 10
        d = [0] * 10
        a[0] = 1
        d[0] = a[0] + durations_arr[seq[0]] - 1
        for i in range(1, 10):
            a[i] = d[i-1]
            d[i] = a[i] + durations_arr[seq[i]] - 1
        
        # Build itinerary
        itinerary = []
        for i in range(10):
            city_name = city_dict[seq[i]]
            # Full range for the city
            if a[i] == d[i]:
                day_range_str = "Day %d" % a[i]
            else:
                day_range_str = "Day %d-%d" % (a[i], d[i])
            itinerary.append({"day_range": day_range_str, "place": city_name})
            
            # If not the last city, add flight day entries
            if i < 9:
                # Flight day: same as d[i] (and a[i+1])
                day = d[i]
                # Departure from current city
                itinerary.append({"day_range": "Day %d" % day, "place": city_name})
                # Arrival at next city
                next_city_name = city_dict[seq[i+1]]
                itinerary.append({"day_range": "Day %d" % day, "place": next_city_name})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()