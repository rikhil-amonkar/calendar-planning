from z3 import *

def solve_itinerary():
    # Cities and days
    cities = ['London', 'Oslo', 'Split', 'Porto']
    n_days = 16
    
    # Create solver
    s = Solver()
    
    # Variables: day_city[day][city] = True if in city on that day
    day_city = [[Bool(f"day_{day}_city_{city}") for city in cities] for day in range(n_days)]
    
    # Direct flight connections
    connections = {
        ('London', 'Oslo'), ('Oslo', 'London'),
        ('Split', 'Oslo'), ('Oslo', 'Split'),
        ('Oslo', 'Porto'), ('Porto', 'Oslo'),
        ('London', 'Split'), ('Split', 'London')
    }
    
    # Constraints
    for day in range(n_days):
        # At least one city per day
        s.add(Or([day_city[day][i] for i in range(len(cities))]))
        
        # If two cities on same day, must be connected
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                city1 = cities[i]
                city2 = cities[j]
                s.add(Implies(
                    And(day_city[day][i], day_city[day][j]),
                    Or((city1, city2) in connections, (city2, city1) in connections)
                ))
    
    # Split constraints (days 7-11, 5 days total)
    split_idx = cities.index('Split')
    for day in range(6, 11):  # Days 7-11 (0-based 6-10)
        s.add(day_city[day][split_idx])
    s.add(Sum([If(day_city[day][split_idx], 1, 0) for day in range(n_days)]) == 5)
    
    # London constraints (7 days total, some between 1-7)
    london_idx = cities.index('London')
    s.add(Sum([If(day_city[day][london_idx], 1, 0) for day in range(0, 7)]) >= 1)  # At least 1 day in first 7
    s.add(Sum([If(day_city[day][london_idx], 1, 0) for day in range(n_days)]) == 7)
    
    # Oslo constraints (2 days)
    oslo_idx = cities.index('Oslo')
    s.add(Sum([If(day_city[day][oslo_idx], 1, 0) for day in range(n_days)]) == 2)
    
    # Porto constraints (5 days)
    porto_idx = cities.index('Porto')
    s.add(Sum([If(day_city[day][porto_idx], 1, 0) for day in range(n_days)]) == 5)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(n_days):
            current_day = day + 1  # 1-based
            places = [cities[i] for i in range(len(cities)) if is_true(m.evaluate(day_city[day][i]))]
            itinerary.append({"day": current_day, "place": places})
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Run and print
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))