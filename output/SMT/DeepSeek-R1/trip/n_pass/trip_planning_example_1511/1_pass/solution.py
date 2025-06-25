from z3 import *
import json

def main():
    # Define the cities and their required days
    cities = ['Venice', 'Reykjavik', 'Munich', 'Santorini', 'Manchester', 'Porto', 'Bucharest', 'Tallinn', 'Valencia', 'Vienna']
    req_days = [3, 2, 3, 3, 3, 3, 5, 4, 2, 5]  # corresponding to the cities above
    
    # Index for fixed cities
    idx_munich = cities.index('Munich')  # 2
    idx_santorini = cities.index('Santorini')  # 3
    idx_valencia = cities.index('Valencia')  # 8
    
    # Direct flights as tuples of indices (undirected, so we include both directions)
    direct_flights_tuples = [
        ('Bucharest', 'Manchester'),
        ('Munich', 'Venice'),
        ('Santorini', 'Manchester'),
        ('Vienna', 'Reykjavik'),
        ('Venice', 'Santorini'),
        ('Munich', 'Porto'),
        ('Valencia', 'Vienna'),
        ('Manchester', 'Vienna'),
        ('Porto', 'Vienna'),
        ('Venice', 'Manchester'),
        ('Santorini', 'Vienna'),
        ('Munich', 'Manchester'),
        ('Munich', 'Reykjavik'),
        ('Bucharest', 'Valencia'),
        ('Venice', 'Vienna'),
        ('Bucharest', 'Vienna'),
        ('Porto', 'Manchester'),
        ('Munich', 'Vienna'),
        ('Valencia', 'Porto'),
        ('Munich', 'Bucharest'),
        ('Tallinn', 'Munich'),
        ('Santorini', 'Bucharest'),
        ('Munich', 'Valencia')
    ]
    
    # Convert city names to indices for the direct flights
    direct_flights_indices = []
    for a, b in direct_flights_tuples:
        idx_a = cities.index(a)
        idx_b = cities.index(b)
        direct_flights_indices.append((idx_a, idx_b))
        direct_flights_indices.append((idx_b, idx_a))
    
    n = len(cities)
    s = Solver()
    
    # Sequence of cities: array of n integers, each in [0, n-1], distinct
    seq = [Int(f'seq_{i}') for i in range(n)]
    for i in range(n):
        s.add(seq[i] >= 0, seq[i] < n)
    s.add(Distinct(seq))
    
    # Start day for each position in the sequence
    start_day = [Int(f'start_{i}') for i in range(n)]
    s.add(start_day[0] == 1)  # first city starts on day 1
    
    # Array for required days (Z3 array)
    req_array = Array('req_array', IntSort(), IntSort())
    for j in range(n):
        s.add(req_array[j] == req_days[j])
    
    # Chain the start days: start_day[i+1] = start_day[i] + (req_days[seq[i]] - 1)
    for i in range(n-1):
        s.add(start_day[i+1] == start_day[i] + (req_array[seq[i]] - 1))
    
    # Fixed start days for specific cities
    for i in range(n):
        s.add(Implies(seq[i] == idx_munich, start_day[i] == 4))
        s.add(Implies(seq[i] == idx_santorini, start_day[i] == 8))
        s.add(Implies(seq[i] == idx_valencia, start_day[i] == 14))
    
    # Last city must end at day 24
    last_end = start_day[n-1] + (req_array[seq[n-1]] - 1)
    s.add(last_end == 24)
    
    # Direct flight constraints between consecutive cities
    for i in range(n-1):
        constraints = []
        for (a, b) in direct_flights_indices:
            constraints.append(And(seq[i] == a, seq[i+1] == b))
        s.add(Or(constraints))
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        seq_val = [model.evaluate(seq[i]).as_long() for i in range(n)]
        start_day_val = [model.evaluate(start_day[i]).as_long() for i in range(n)]
        
        # Build itinerary
        itinerary = []
        for i in range(n):
            city_idx = seq_val[i]
            city_name = cities[city_idx]
            s_i = start_day_val[i]
            e_i = s_i + req_days[city_idx] - 1
            if s_i == e_i:
                day_range_str = f"Day {s_i}"
            else:
                day_range_str = f"Day {s_i}-{e_i}"
            itinerary.append({"day_range": day_range_str, "place": city_name})
            
            if i < n-1:
                flight_day = start_day_val[i+1]
                itinerary.append({"day_range": f"Day {flight_day}", "place": city_name})
                next_city_idx = seq_val[i+1]
                next_city_name = cities[next_city_idx]
                itinerary.append({"day_range": f"Day {flight_day}", "place": next_city_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()