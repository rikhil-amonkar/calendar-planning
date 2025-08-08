from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Porto', 'Prague', 'Reykjavik', 'Santorini', 'Amsterdam', 'Munich']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Porto': ['Amsterdam', 'Munich'],
        'Munich': ['Amsterdam', 'Porto', 'Reykjavik', 'Prague'],
        'Reykjavik': ['Amsterdam', 'Munich', 'Prague'],
        'Amsterdam': ['Porto', 'Munich', 'Reykjavik', 'Santorini', 'Prague'],
        'Prague': ['Reykjavik', 'Amsterdam', 'Munich'],
        'Santorini': ['Amsterdam']
    }
    
    # Total days
    total_days = 16
    
    # Create Z3 variables: for each day, which city is visited
    day_city = [[Bool(f"day_{day+1}_city_{city}") for city in cities] for day in range(total_days)]
    
    s = Solver()
    
    # Constraint: each day, the person is in at least one city and at most two
    for day in range(total_days):
        # At least one city per day
        s.add(Or([day_city[day][i] for i in range(len(cities))]))
        # At most two cities per day
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                for k in range(j+1, len(cities)):
                    s.add(Not(And(day_city[day][i], day_city[day][j], day_city[day][k])))
    
    # Flight constraints: if two cities on a day, they must be connected
    for day in range(total_days):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                city_i = cities[i]
                city_j = cities[j]
                s.add(Implies(
                    And(day_city[day][i], day_city[day][j]),
                    Or(city_j in direct_flights[city_i], city_i in direct_flights[city_j])
                ))
    
    # Total days per city constraints
    city_days_required = {
        'Porto': 5,
        'Prague': 4,
        'Reykjavik': 4,
        'Santorini': 2,
        'Amsterdam': 2,
        'Munich': 4
    }
    
    for city_idx, city in enumerate(cities):
        required_days = city_days_required[city]
        total = 0
        for day in range(total_days):
            total += If(day_city[day][city_idx], 1, 0)
        s.add(total == required_days)
    
    # Event constraints:
    # Wedding in Reykjavik between day 4 and 7 (inclusive) (0-based days 3-6)
    reykjavik_idx = city_to_idx['Reykjavik']
    s.add(Or([day_city[day][reykjavik_idx] for day in [3, 4, 5, 6]]))
    
    # Conference in Amsterdam on day 14 and 15 (0-based days 13 and 14)
    amsterdam_idx = city_to_idx['Amsterdam']
    s.add(day_city[13][amsterdam_idx])
    s.add(day_city[14][amsterdam_idx])
    
    # Meet friend in Munich between day 7 and 10 (0-based days 6-9)
    munich_idx = city_to_idx['Munich']
    s.add(Or([day_city[day][munich_idx] for day in [6, 7, 8, 9]]))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        for day in range(total_days):
            current_cities = []
            for city_idx in range(len(cities)):
                if is_true(model.eval(day_city[day][city_idx])):
                    current_cities.append(cities[city_idx])
            place = current_cities[0] if len(current_cities) == 1 else f"{current_cities[0]},{current_cities[1]}"
            itinerary.append({'day': day + 1, 'place': place})
        
        # Verify no gaps or overlaps
        prev_day = None
        for entry in itinerary:
            day = entry['day']
            place = entry['place']
            if prev_day is not None and day != prev_day + 1:
                return {"error": "Gap or overlap in days"}
            prev_day = day
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))