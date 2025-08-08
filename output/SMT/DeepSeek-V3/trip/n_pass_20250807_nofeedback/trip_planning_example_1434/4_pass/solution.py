from z3 import *
import json

def solve_itinerary():
    # Cities to visit
    cities = ['Rome', 'Mykonos', 'Lisbon', 'Frankfurt', 'Nice', 'Stuttgart', 'Venice', 'Dublin', 'Bucharest', 'Seville']
    
    # Required days in each city
    required_days = {
        'Rome': 3,
        'Mykonos': 2,
        'Lisbon': 2,
        'Frankfurt': 5,
        'Nice': 3,
        'Stuttgart': 4,
        'Venice': 4,
        'Dublin': 2,
        'Bucharest': 2,
        'Seville': 5
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ('Rome', 'Stuttgart'),
        ('Venice', 'Rome'),
        ('Dublin', 'Bucharest'),
        ('Mykonos', 'Rome'),
        ('Seville', 'Lisbon'),
        ('Frankfurt', 'Venice'),
        ('Venice', 'Stuttgart'),
        ('Bucharest', 'Lisbon'),
        ('Nice', 'Mykonos'),
        ('Venice', 'Lisbon'),
        ('Dublin', 'Lisbon'),
        ('Venice', 'Nice'),
        ('Rome', 'Seville'),
        ('Frankfurt', 'Rome'),
        ('Nice', 'Dublin'),
        ('Rome', 'Bucharest'),
        ('Frankfurt', 'Dublin'),
        ('Rome', 'Dublin'),
        ('Venice', 'Dublin'),
        ('Rome', 'Lisbon'),
        ('Frankfurt', 'Lisbon'),
        ('Nice', 'Rome'),
        ('Frankfurt', 'Nice'),
        ('Frankfurt', 'Stuttgart'),
        ('Frankfurt', 'Bucharest'),
        ('Lisbon', 'Stuttgart'),
        ('Nice', 'Lisbon'),
        ('Seville', 'Dublin')
    ]
    
    # Create a set of direct flight pairs for easy lookup
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Create Z3 variables for each day (1..23)
    # day_city[d][c] is true if we are in city c on day d
    days = 23
    day_city = [[Bool(f"day_{day+1}_city_{city}") for city in cities] for day in range(days)]
    
    s = Solver()
    
    # Constraint 1: Total days in each city equals required_days
    for city_idx, city in enumerate(cities):
        total = Sum([If(day_city[day][city_idx], 1, 0) for day in range(days)])
        s.add(total == required_days[city])
    
    # Constraint 2: If consecutive days are in different cities, there must be a flight
    for day in range(days - 1):
        for city1_idx in range(len(cities)):
            for city2_idx in range(len(cities)):
                if city1_idx != city2_idx:
                    city1 = cities[city1_idx]
                    city2 = cities[city2_idx]
                    if (city1, city2) not in flight_pairs:
                        s.add(Not(And(day_city[day][city1_idx], day_city[day+1][city2_idx])))
    
    # Fixed events
    # Wedding in Frankfurt between day 1-5 (1-based)
    s.add(Or([day_city[day][cities.index('Frankfurt')] for day in range(0, 5)]))
    
    # Conference in Seville between day 13-17 (1-based: days 12-16 in 0-based)
    s.add(Or([day_city[day][cities.index('Seville')] for day in range(12, 17)]))
    
    # Meet friends in Mykonos between day 10-11 (1-based: days 9-10)
    s.add(Or(day_city[9][cities.index('Mykonos')], day_city[10][cities.index('Mykonos')]))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(days):
            current_day = day + 1
            places = []
            for city_idx, city in enumerate(cities):
                if is_true(m.evaluate(day_city[day][city_idx])):
                    places.append(city)
            if len(places) == 1:
                itinerary.append({"day": current_day, "place": places[0]})
            else:
                itinerary.append({"day": current_day, "place": ", ".join(places)})
        
        result = {"itinerary": itinerary}
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No valid itinerary found."}, indent=2)

print(solve_itinerary())