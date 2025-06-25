from z3 import *
import json

def main():
    # Define the cities
    cities = ['Brussels', 'Rome', 'Dubrovnik', 'Geneva', 'Budapest', 'Riga', 'Valencia']
    City, city_const = EnumSort('City', cities)
    (Brussels, Rome, Dubrovnik, Geneva, Budapest, Riga, Valencia) = city_const
    city_map = {name: const for name, const in zip(cities, city_const)}
    
    # Define the direct flight edges
    edges_str = [
        ('Brussels', 'Valencia'),
        ('Rome', 'Valencia'),
        ('Brussels', 'Geneva'),
        ('Rome', 'Geneva'),
        ('Dubrovnik', 'Geneva'),
        ('Valencia', 'Geneva'),
        ('Rome', 'Riga'),
        ('Geneva', 'Budapest'),
        ('Riga', 'Brussels'),
        ('Rome', 'Budapest'),
        ('Rome', 'Brussels'),
        ('Brussels', 'Budapest'),
        ('Dubrovnik', 'Rome')
    ]
    edges = []
    for a, b in edges_str:
        edges.append((city_map[a], city_map[b]))
    
    n = len(cities)
    s = Solver()
    
    # Sequence of cities (permutation)
    seq = [Const(f'seq_{i}', City) for i in range(n)]
    s.add(Distinct(seq))
    
    # Flight constraints: consecutive cities must have a direct flight
    for i in range(n-1):
        cons = []
        for a, b in edges:
            cons.append(And(seq[i] == a, seq[i+1] == b))
            cons.append(And(seq[i] == b, seq[i+1] == a))
        s.add(Or(cons))
    
    # Required days for each city
    req_vals = {
        Brussels: 5,
        Rome: 2,
        Dubrovnik: 3,
        Geneva: 5,
        Budapest: 2,
        Riga: 4,
        Valencia: 2
    }
    req_fun = Function('req', City, IntSort())
    for city, days in req_vals.items():
        s.add(req_fun(city) == days)
    
    # Start and end days for each city segment
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]
    
    # First segment starts on day 1
    s.add(start[0] == 1)
    s.add(end[0] == start[0] + req_fun(seq[0]) - 1)
    
    # Subsequent segments start where the previous ends
    for i in range(1, n):
        s.add(start[i] == end[i-1])
        s.add(end[i] == start[i] + req_fun(seq[i]) - 1)
    
    # Workshop and meeting constraints
    for i in range(n):
        # Brussels must include a day between 7 and 11
        s.add(If(seq[i] == Brussels, And(start[i] <= 11, end[i] >= 7), True))
        # Budapest must include a day between 16 and 17
        s.add(If(seq[i] == Budapest, And(start[i] <= 17, end[i] >= 16), True))
        # Riga must include a day between 4 and 7
        s.add(If(seq[i] == Riga, And(start[i] <= 7, end[i] >= 4), True))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        seq_val = [m.eval(seq[i]) for i in range(n)]
        start_val = [m.eval(start[i]).as_long() for i in range(n)]
        end_val = [m.eval(end[i]).as_long() for i in range(n)]
        
        # Map enum values to city names
        city_names = []
        for c in seq_val:
            for idx, const in enumerate(city_const):
                if m.eval(c).eq(m.eval(const)):
                    city_names.append(cities[idx])
                    break
        
        # Build itinerary
        itinerary = []
        for i in range(n):
            s_i = start_val[i]
            e_i = end_val[i]
            if s_i == e_i:
                day_range = f"Day {s_i}"
            else:
                day_range = f"Day {s_i}-{e_i}"
            itinerary.append({"day_range": day_range, "place": city_names[i]})
            
            if i < n-1:
                itinerary.append({"day_range": f"Day {e_i}", "place": city_names[i]})
                itinerary.append({"day_range": f"Day {e_i}", "place": city_names[i+1]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()