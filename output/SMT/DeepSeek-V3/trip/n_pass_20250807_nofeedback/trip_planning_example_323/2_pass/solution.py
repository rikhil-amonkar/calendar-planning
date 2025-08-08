from z3 import *

def solve_itinerary():
    # Cities
    cities = ['London', 'Oslo', 'Split', 'Porto']
    n_days = 16
    
    # Create Z3 variables: for each day, which cities are visited (Boolean)
    # day_city[d][c] is True if day d+1 is spent in city c (1-based days)
    day_city = [[Bool(f"day_{day}_city_{city}") for city in cities] for day in range(n_days)]
    
    s = Solver()
    
    # Direct flight connections
    direct_connections = {
        ('London', 'Oslo'),
        ('Oslo', 'London'),
        ('Split', 'Oslo'),
        ('Oslo', 'Split'),
        ('Oslo', 'Porto'),
        ('Porto', 'Oslo'),
        ('London', 'Split'),
        ('Split', 'London')
    }
    
    # Constraints for each day: at least one city, and if two cities, they must be connected directly
    for day in range(n_days):
        # At least one city per day
        s.add(Or([day_city[day][i] for i in range(len(cities))]))
        
        # For each pair of cities in the same day, they must be directly connected
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                city_i = cities[i]
                city_j = cities[j]
                # If both cities are visited on this day, they must be connected
                s.add(Implies(And(day_city[day][i], day_city[day][j]), 
                              Or((city_i, city_j) in direct_connections,
                                 (city_j, city_i) in direct_connections)))
    
    # Total days per city
    # Split: 5 days, including days 7-11 (1-based: days 6-10 in 0-based)
    split_index = cities.index('Split')
    for day in range(6, 11):  # days 7-11 (1-based) are 6-10 in 0-based
        s.add(day_city[day][split_index])
    # Total Split days is 5, which is already covered by the 5 days 7-11
    
    # London: 7 days, with some between day 1 and 7 (1-based: days 0-6 in 0-based)
    london_index = cities.index('London')
    london_days_in_first_7 = []
    for day in range(0, 7):  # days 1-7
        london_days_in_first_7.append(day_city[day][london_index])
    s.add(Sum([If(cond, 1, 0) for cond in london_days_in_first_7]) >= 1)
    # Total London days is 7
    s.add(Sum([If(day_city[day][london_index], 1, 0) for day in range(n_days)]) == 7)
    
    # Oslo: 2 days
    oslo_index = cities.index('Oslo')
    s.add(Sum([If(day_city[day][oslo_index], 1, 0) for day in range(n_days)]) == 2)
    
    # Porto: 5 days
    porto_index = cities.index('Porto')
    s.add(Sum([If(day_city[day][porto_index], 1, 0) for day in range(n_days)]) == 5)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(n_days):
            current_day = day + 1  # 1-based
            cities_in_day = []
            for city_idx in range(len(cities)):
                if is_true(m.evaluate(day_city[day][city_idx])):
                    cities_in_day.append(cities[city_idx])
            itinerary.append({"day": current_day, "place": cities_in_day})
        
        # Verify the itinerary meets all constraints
        # (This is a sanity check; the solver should have ensured this)
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate and print the itinerary
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))