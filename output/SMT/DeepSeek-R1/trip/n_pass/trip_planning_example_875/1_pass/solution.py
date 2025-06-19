from z3 import *

def main():
    # Mapping of city names to indices
    cities = ['Stuttgart', 'Edinburgh', 'Athens', 'Split', 'Krakow', 'Venice', 'Mykonos']
    required_stays = [3, 4, 4, 2, 4, 5, 4]  # Corresponding to cities list
    
    # Direct flight pairs (undirected)
    flight_pairs = [
        ('Krakow', 'Split'),
        ('Split', 'Athens'),
        ('Edinburgh', 'Krakow'),
        ('Venice', 'Stuttgart'),
        ('Krakow', 'Stuttgart'),
        ('Edinburgh', 'Stuttgart'),
        ('Stuttgart', 'Athens'),
        ('Venice', 'Edinburgh'),
        ('Athens', 'Mykonos'),
        ('Venice', 'Athens'),
        ('Stuttgart', 'Split'),
        ('Edinburgh', 'Athens')
    ]
    
    # Create a mapping from city name to index
    mapping = {city: idx for idx, city in enumerate(cities)}
    flight_set_num = set()
    for a, b in flight_pairs:
        a_num = mapping[a]
        b_num = mapping[b]
        flight_set_num.add((min(a_num, b_num), max(a_num, b_num)))
    
    # Initialize Z3 solver
    s = Solver()
    
    # Define the permutation of cities: city[i] for i in 0..6
    city_vars = [Int(f'city_{i}') for i in range(7)]
    for i in range(7):
        s.add(city_vars[i] >= 0, city_vars[i] < 7)
    s.add(Distinct(city_vars))
    
    # Flight constraints between consecutive cities
    for i in range(6):
        c1 = city_vars[i]
        c2 = city_vars[i+1]
        conds = []
        for (a, b) in flight_set_num:
            conds.append(And(c1 == a, c2 == b))
            conds.append(And(c1 == b, c2 == a))
        s.add(Or(conds))
    
    # Compute cumulative flight days d[0..6]
    d = [0] * 7
    d[0] = 0  # d0 is 0
    d[1] = required_stays[city_vars[0]]  # d1 = stay of first city
    for i in range(1, 6):
        d[i+1] = d[i] + (required_stays[city_vars[i]] - 1)
    d[6] = d[5] + (required_stays[city_vars[5]] - 1)  # d6 for the sixth flight day
    
    # Function to get start and end days for a city
    def get_start_end(city_num):
        start_expr = None
        end_expr = None
        for i in range(7):
            cond = (city_vars[i] == city_num)
            if i == 0:
                s_i = 1
                e_i = d[1]
            elif i == 6:
                s_i = d[6]
                e_i = 20
            else:
                s_i = d[i]
                e_i = d[i+1]
            if start_expr is None:
                start_expr = s_i
                end_expr = e_i
            else:
                start_expr = If(cond, s_i, start_expr)
                end_expr = If(cond, e_i, end_expr)
        return (start_expr, end_expr)
    
    # Constraints for specific cities
    start_stuttgart, end_stuttgart = get_start_end(0)  # Stuttgart index 0
    s.add(start_stuttgart <= 13, end_stuttgart >= 11)
    
    start_split, end_split = get_start_end(3)  # Split index 3
    s.add(start_split <= 14, end_split >= 13)
    
    start_krakow, end_krakow = get_start_end(4)  # Krakow index 4
    s.add(start_krakow <= 11, end_krakow >= 8)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        # Extract the city order
        order = [m.evaluate(city_vars[i]).as_long() for i in range(7)]
        city_names = [cities[idx] for idx in order]
        
        # Compute actual flight days
        d_vals = [0] * 7
        d_vals[0] = 0
        d_vals[1] = required_stays[order[0]]
        for i in range(1, 6):
            d_vals[i+1] = d_vals[i] + (required_stays[order[i]] - 1)
        d_vals[6] = d_vals[5] + (required_stays[order[5]] - 1)
        
        # Build itinerary
        itinerary = []
        for i in range(7):
            cname = city_names[i]
            if i == 0:
                start = 1
                end = d_vals[1]
            elif i == 6:
                start = d_vals[6]
                end = 20
            else:
                start = d_vals[i]
                end = d_vals[i+1]
            
            # Add consecutive stay
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": cname})
            
            # Add flight day entries if not the last city
            if i < 6:
                itinerary.append({"day_range": f"Day {end}", "place": cname})
                itinerary.append({"day_range": f"Day {end}", "place": city_names[i+1]})
        
        # Output result
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()