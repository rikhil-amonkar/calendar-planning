from z3 import *
import json

def solve_itinerary():
    # Cities to visit
    cities = ['Rome', 'Mykonos', 'Lisbon', 'Frankfurt', 'Nice', 'Stuttgart', 'Venice', 'Dublin', 'Bucharest', 'Seville']
    city_index = {city:i for i,city in enumerate(cities)}
    
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
    
    # Create flight connections graph
    flight_graph = {city:set() for city in cities}
    for a,b in direct_flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)
    
    # Total days
    total_days = 23
    
    # Create Z3 variables
    s = Solver()
    
    # Variables for arrival and departure days for each city
    arrival = {city: Int(f'arrival_{city}') for city in cities}
    departure = {city: Int(f'departure_{city}') for city in cities}
    
    # Constraints for arrival and departure days
    for city in cities:
        s.add(arrival[city] >= 1)
        s.add(departure[city] <= total_days)
        s.add(departure[city] >= arrival[city])
        # Duration constraint
        s.add(departure[city] - arrival[city] + 1 == required_days[city])
    
    # Fixed events
    # Wedding in Frankfurt between day 1-5
    s.add(arrival['Frankfurt'] <= 1)
    s.add(departure['Frankfurt'] >= 5)
    
    # Conference in Seville between day 13-17
    s.add(arrival['Seville'] <= 13)
    s.add(departure['Seville'] >= 17)
    
    # Meet friends in Mykonos between day 10-11
    s.add(Or(
        And(arrival['Mykonos'] <= 10, departure['Mykonos'] >= 10),
        And(arrival['Mykonos'] <= 11, departure['Mykonos'] >= 11)
    ))
    
    # Ensure cities are visited in sequence with valid flights
    # We'll model this by creating an ordering of city visits
    visit_order = [Int(f'visit_{i}') for i in range(len(cities))]
    s.add(Distinct(visit_order))
    for i in range(len(cities)):
        s.add(visit_order[i] >= 0)
        s.add(visit_order[i] < len(cities))
    
    # Constraints for flight connections between consecutive visits
    for i in range(len(cities)-1):
        current_city = cities[visit_order[i]]
        next_city = cities[visit_order[i+1]]
        # Departure from current city must be before arrival at next city
        s.add(departure[current_city] <= arrival[next_city])
        # There must be a flight between them
        s.add(Or([next_city in flight_graph[current_city], current_city in flight_graph[next_city]]))
    
    # Ensure all cities are visited exactly once
    for city in cities:
        s.add(Or([visit_order[i] == city_index[city] for i in range(len(cities))]))
    
    if s.check() == sat:
        m = s.model()
        # Extract the visit order
        ordered_visits = sorted([(m[visit_order[i]].as_long(), cities[i]) for i in range(len(cities))], key=lambda x: x[0])
        visit_sequence = [city for (order,city) in ordered_visits]
        
        # Build itinerary
        itinerary = []
        current_day = 1
        for i in range(len(visit_sequence)):
            city = visit_sequence[i]
            arr_day = m[arrival[city]].as_long()
            dep_day = m[departure[city]].as_long()
            
            # Add days in this city
            for day in range(arr_day, dep_day + 1):
                itinerary.append({"day": day, "place": city})
            
            # If not last city, add flight day to next city
            if i < len(visit_sequence) - 1:
                next_city = visit_sequence[i+1]
                flight_day = dep_day
                itinerary.append({"day": flight_day, "place": f"{city}, {next_city}"})
        
        # Group consecutive days in same city
        grouped_itinerary = []
        current_entry = None
        for entry in itinerary:
            if current_entry is None:
                current_entry = entry.copy()
                current_entry['day_range'] = f"Day {entry['day']}"
            elif entry['place'] == current_entry['place'] and entry['day'] == current_entry['day'] + 1:
                current_entry['day_range'] = f"Day {current_entry['day_range'].split(' ')[1]}-{entry['day']}"
                current_entry['day'] = entry['day']
            else:
                grouped_itinerary.append(current_entry)
                current_entry = entry.copy()
                current_entry['day_range'] = f"Day {entry['day']}"
        if current_entry is not None:
            grouped_itinerary.append(current_entry)
        
        result = {"itinerary": grouped_itinerary}
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No valid itinerary found."}, indent=2)

print(solve_itinerary())