from z3 import *

def main():
    # Map of cities
    cities = ['Paris', 'Florence', 'Barcelona', 'Tallinn', 'Vilnius', 'Amsterdam', 'Venice', 'Warsaw', 'Hamburg', 'Salzburg']
    n_cities = len(cities)
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    
    # Graph connections
    graph_conn = {
        'Paris': ['Florence', 'Barcelona', 'Tallinn', 'Amsterdam', 'Hamburg', 'Salzburg'],
        'Florence': ['Paris', 'Barcelona', 'Venice', 'Warsaw'],
        'Barcelona': ['Paris', 'Florence', 'Tallinn'],
        'Tallinn': ['Paris', 'Barcelona', 'Vilnius'],
        'Vilnius': ['Tallinn', 'Warsaw'],
        'Amsterdam': ['Paris', 'Hamburg'],
        'Venice': ['Florence', 'Salzburg'],
        'Warsaw': ['Florence', 'Vilnius', 'Hamburg'],
        'Hamburg': ['Paris', 'Amsterdam', 'Warsaw', 'Salzburg'],
        'Salzburg': ['Paris', 'Venice', 'Hamburg']
    }
    
    # Convert graph to integer indices
    allowed_edges = []
    for city_name, neighbors in graph_conn.items():
        a = city_to_int[city_name]
        for nb in neighbors:
            b = city_to_int[nb]
            allowed_edges.append((a, b))
    
    n_stays = 11
    city_vars = [Int(f'city_{i}') for i in range(n_stays)]
    dur_vars = [Int(f'dur_{i}') for i in range(n_stays-1)]
    total_first_10 = Sum(dur_vars)
    dur_last = 24 - total_first_10
    
    s = Solver()
    
    # First and last stay must be Paris (index 0)
    s.add(city_vars[0] == 0)
    s.add(city_vars[10] == 0)
    
    # Middle 9 stays: distinct and in 1..9 (non-Paris)
    for i in range(1, 10):
        s.add(city_vars[i] >= 1, city_vars[i] <= 9)
    s.add(Distinct([city_vars[i] for i in range(1, 10)]))
    
    # Connectivity constraints for consecutive stays
    for i in range(n_stays - 1):
        edge_conds = []
        for (a, b) in allowed_edges:
            edge_conds.append(And(city_vars[i] == a, city_vars[i+1] == b))
        s.add(Or(edge_conds))
    
    # Duration constraints: first 10 stays at least 1 night, middle 9 stays (non-Paris) at least 2 nights
    for i in range(len(dur_vars)):
        s.add(dur_vars[i] >= 1)
        if i >= 1 and i <= 9:
            s.add(dur_vars[i] >= 2)
    
    # Last stay must be at least 1 night
    s.add(dur_last >= 1)
    # Total nights in Paris (first and last) must be at least 2
    s.add(dur_vars[0] + dur_last >= 2)
    # Total of first 10 stays must be <= 23 (so last stay is at least 1)
    s.add(total_first_10 <= 23)
    
    if s.check() == sat:
        m = s.model()
        city_vals = [m[city_vars[i]].as_long() for i in range(n_stays)]
        dur_vals = [m[dur_vars[i]].as_long() for i in range(n_stays-1)]
        dur_vals.append(24 - sum(dur_vals))
        
        start_days = [1]
        for i in range(n_stays-1):
            start_days.append(start_days[-1] + dur_vals[i])
        
        itinerary = []
        for i in range(n_stays):
            s_day = start_days[i]
            d_val = dur_vals[i]
            if d_val == 1:
                day_range = f"Day {s_day}"
            else:
                day_range = f"Day {s_day}-{s_day + d_val - 1}"
            place = cities[city_vals[i]]
            itinerary.append({'day_range': day_range, 'place': place})
        
        print(f"Plan found: {itinerary}")
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()