import z3
import json
from collections import defaultdict

def main():
    cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
    n_cities = len(cities)
    n_days = 15
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    edges = [
        ('Helsinki', 'Riga'),
        ('Riga', 'Tallinn'),
        ('Vienna', 'Helsinki'),
        ('Riga', 'Dublin'),
        ('Vienna', 'Riga'),
        ('Reykjavik', 'Vienna'),
        ('Helsinki', 'Dublin'),
        ('Tallinn', 'Dublin'),
        ('Reykjavik', 'Helsinki'),
        ('Reykjavik', 'Dublin'),
        ('Helsinki', 'Tallinn'),
        ('Vienna', 'Dublin')
    ]
    allowed_edges_set = set()
    for (u, v) in edges:
        u_idx = city_to_index[u]
        v_idx = city_to_index[v]
        allowed_edges_set.add((u_idx, v_idx))
        allowed_edges_set.add((v_idx, u_idx))
    
    start_city = z3.Int('start_city')
    loc = [z3.Int(f'loc_{i}') for i in range(n_days)]
    flight_taken = [z3.Bool(f'flight_taken_{i}') for i in range(n_days)]
    
    optimizer = z3.Optimize()
    
    optimizer.add(start_city >= 0, start_city < n_cities)
    for i in range(n_days):
        optimizer.add(loc[i] >= 0, loc[i] < n_cities)
    
    # Day 1 constraints
    optimizer.add(z3.Implies(flight_taken[0], start_city != loc[0]))
    optimizer.add(z3.Implies(flight_taken[0], 
                             z3.Or([z3.And(start_city == u, loc[0] == v) for (u, v) in allowed_edges_set])))
    optimizer.add(z3.Implies(z3.Not(flight_taken[0]), loc[0] == start_city))
    
    # Subsequent days
    for i in range(1, n_days):
        optimizer.add(z3.Implies(flight_taken[i], loc[i-1] != loc[i]))
        optimizer.add(z3.Implies(flight_taken[i], 
                                 z3.Or([z3.And(loc[i-1] == u, loc[i] == v) for (u, v) in allowed_edges_set])))
        optimizer.add(z3.Implies(z3.Not(flight_taken[i]), loc[i] == loc[i-1]))
    
    # Total nights per city
    total_nights = [0] * n_cities
    for c in range(n_cities):
        total_nights[c] = z3.Sum([z3.If(loc[i] == c, 1, 0) for i in range(n_days)])
    
    optimizer.add(total_nights[city_to_index['Dublin']] == 5)
    optimizer.add(total_nights[city_to_index['Helsinki']] == 3)
    optimizer.add(total_nights[city_to_index['Riga']] == 3)
    optimizer.add(total_nights[city_to_index['Reykjavik']] == 2)
    optimizer.add(total_nights[city_to_index['Vienna']] == 2)
    optimizer.add(total_nights[city_to_index['Tallinn']] == 5)
    
    # Event constraints
    vienna_idx = city_to_index['Vienna']
    optimizer.add(loc[1] == vienna_idx)  # Night of day 2
    optimizer.add(loc[2] == vienna_idx)  # Night of day 3
    
    helsinki_idx = city_to_index['Helsinki']
    optimizer.add(z3.Or(loc[2] == helsinki_idx,  # Night of day 3
                       loc[3] == helsinki_idx,   # Night of day 4
                       loc[4] == helsinki_idx))  # Night of day 5
    
    tallinn_idx = city_to_index['Tallinn']
    tallinn_constraint = z3.Or([loc[i] == tallinn_idx for i in range(6, 11)])
    optimizer.add(tallinn_constraint)  # Nights of days 7-11
    
    # Minimize flights
    num_flights = z3.Sum([z3.If(ft, 1, 0) for ft in flight_taken])
    optimizer.minimize(num_flights)
    
    if optimizer.check() == z3.sat:
        model = optimizer.model()
        start_city_val = model.evaluate(start_city).as_long()
        loc_vals = [model.evaluate(loc[i]).as_long() for i in range(n_days)]
        
        # Build itinerary from night stays
        day_assignments = [cities[loc_vals[0]]]  # Day 1
        for i in range(1, n_days):
            day_assignments.append(cities[loc_vals[i]])
        
        # Group consecutive days
        itinerary = []
        current_city = day_assignments[0]
        start_day = 1
        for day in range(1, n_days+1):
            if day == n_days or day_assignments[day] != day_assignments[day-1]:
                end_day = day
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                itinerary.append({
                    "day_range": day_range,
                    "place": current_city
                })
                if day < n_days:
                    current_city = day_assignments[day]
                    start_day = day+1
        
        # Sort by start day
        itinerary_sorted = sorted(itinerary, key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
        result = {"itinerary": itinerary_sorted}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()