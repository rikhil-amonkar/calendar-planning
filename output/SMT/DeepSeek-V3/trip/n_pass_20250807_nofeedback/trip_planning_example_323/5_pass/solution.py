from z3 import *

def solve_itinerary():
    # Cities and days
    cities = ['London', 'Oslo', 'Split', 'Porto']
    n_days = 16
    
    # Create solver
    s = Solver()
    
    # Variables: day_city[day][city] = True if in city on that day
    day_city = [[Bool(f"day_{day}_city_{city}") for city in cities] for day in range(n_days)]
    
    # Direct flight connections (bidirectional)
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
    
    # Split constraints (must be days 7-11, exactly 5 days)
    split_idx = cities.index('Split')
    for day in range(6, 11):  # Days 7-11 (0-based 6-10)
        s.add(day_city[day][split_idx])
    s.add(Sum([If(day_city[day][split_idx], 1, 0) for day in range(n_days)]) == 5)
    
    # London constraints (7 days total, at least 1 between days 1-7)
    london_idx = cities.index('London')
    s.add(Sum([If(day_city[day][london_idx], 1, 0) for day in range(7)]) >= 1)
    s.add(Sum([If(day_city[day][london_idx], 1, 0) for day in range(n_days)]) == 7)
    
    # Oslo constraints (2 days total)
    oslo_idx = cities.index('Oslo')
    s.add(Sum([If(day_city[day][oslo_idx], 1, 0) for day in range(n_days)]) == 2)
    
    # Porto constraints (5 days total)
    porto_idx = cities.index('Porto')
    s.add(Sum([If(day_city[day][porto_idx], 1, 0) for day in range(n_days)]) == 5)
    
    # Additional constraints to prevent invalid transitions
    for day in range(1, n_days):
        # Get cities from previous day
        prev_day = day - 1
        for city1 in cities:
            for city2 in cities:
                if city1 != city2 and (city1, city2) not in connections:
                    # Cannot transition directly between unconnected cities
                    s.add(Implies(
                        And(day_city[prev_day][cities.index(city1)], day_city[day][cities.index(city2)]),
                        Or([day_city[day][cities.index(c)] for c in cities if (city1, c) in connections or (c, city1) in connections])
                    ))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_places = []
        start_day = 1
        
        for day in range(n_days):
            places = [cities[i] for i in range(len(cities)) if is_true(m.evaluate(day_city[day][i]))]
            
            if places != current_places:
                if current_places:
                    itinerary.append({
                        "day_range": f"Day {start_day}-{day}",
                        "place": ", ".join(current_places)
                    })
                current_places = places
                start_day = day + 1
        
        # Add last segment
        if current_places:
            itinerary.append({
                "day_range": f"Day {start_day}-{n_days}",
                "place": ", ".join(current_places)
            })
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Run and print
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))