import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Prague': 3,
        'Warsaw': 4,
        'Dublin': 3,
        'Athens': 3,
        'Vilnius': 4,
        'Porto': 5,
        'London': 3,
        'Seville': 2,
        'Lisbon': 5,
        'Dubrovnik': 3
    }
    
    city_list = sorted(cities.keys())
    city_to_int = {city: idx for idx, city in enumerate(city_list)}
    int_to_city = {idx: city for idx, city in enumerate(city_list)}
    
    # Direct flights: list of tuples
    direct_flights = [
        ('Warsaw', 'Vilnius'),
        ('Prague', 'Athens'),
        ('London', 'Lisbon'),
        ('Lisbon', 'Porto'),
        ('Prague', 'Lisbon'),
        ('London', 'Dublin'),
        ('Athens', 'Vilnius'),
        ('Athens', 'Dublin'),
        ('Prague', 'London'),
        ('London', 'Warsaw'),
        ('Dublin', 'Seville'),
        ('Seville', 'Porto'),
        ('Lisbon', 'Athens'),
        ('Dublin', 'Porto'),
        ('Athens', 'Warsaw'),
        ('Lisbon', 'Warsaw'),
        ('Porto', 'Warsaw'),
        ('Prague', 'Warsaw'),
        ('Prague', 'Dublin'),
        ('Athens', 'Dubrovnik'),
        ('Lisbon', 'Dublin'),
        ('Dubrovnik', 'Dublin'),
        ('Lisbon', 'Seville'),
        ('London', 'Athens')
    ]
    
    # Create a set of allowed transitions (both directions)
    allowed_transitions = set()
    for a, b in direct_flights:
        allowed_transitions.add((city_to_int[a], city_to_int[b]))
        allowed_transitions.add((city_to_int[b], city_to_int[a]))
    
    # Create Z3 variables for each day
    s = Solver()
    day_vars = [Int(f'day_{i}') for i in range(1, 27)]
    
    # Each day variable must be a valid city index
    for day in day_vars:
        s.add(And(day >= 0, day < len(city_list)))
    
    # Helper function to count days in a city
    def days_in_city(city_idx):
        return Sum([If(day_vars[i] == city_idx, 1, 0) for i in range(26)])
    
    # Fixed constraints with more flexibility
    # Prague: 3 days, workshop between day 1-3 (must include at least one day in this range)
    s.add(Or([day_vars[i] == city_to_int['Prague'] for i in range(0, 3)]))
    
    # London: 3 days, wedding between day 3-5 (must include at least one day in this range)
    s.add(Or([day_vars[i] == city_to_int['London'] for i in range(2, 5)]))
    
    # Lisbon: 5 days, relatives between day 5-9 (must include at least one day in this range)
    s.add(Or([day_vars[i] == city_to_int['Lisbon'] for i in range(4, 9)]))
    
    # Porto: 5 days, conference between day 16-20 (must include at least one day in this range)
    s.add(Or([day_vars[i] == city_to_int['Porto'] for i in range(15, 20)]))
    
    # Warsaw: 4 days, meet friends between day 20-23 (must include at least one day in this range)
    s.add(Or([day_vars[i] == city_to_int['Warsaw'] for i in range(19, 23)]))
    
    # Duration constraints for all cities
    for city, days in cities.items():
        s.add(days_in_city(city_to_int[city]) == days)
    
    # Flight transitions: consecutive days must be either same city or connected by direct flight
    for i in range(25):
        current_day = day_vars[i]
        next_day = day_vars[i+1]
        s.add(Or(
            current_day == next_day,
            And(current_day != next_day, (current_day, next_day) in allowed_transitions)
        ))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 27):
            city_idx = model.evaluate(day_vars[day-1]).as_long()
            itinerary.append({"day": day, "place": int_to_city[city_idx]})
        
        # Verify all constraints are met
        # Count days in each city
        day_counts = {city: 0 for city in city_list}
        for entry in itinerary:
            day_counts[entry['place']] += 1
        
        # Verify durations
        for city, days in cities.items():
            assert day_counts[city] == days, f"{city} duration mismatch"
        
        # Verify fixed constraints
        assert any(itinerary[i]['place'] == 'Prague' for i in range(0, 3)), "Prague workshop not met"
        assert any(itinerary[i]['place'] == 'London' for i in range(2, 5)), "London wedding not met"
        assert any(itinerary[i]['place'] == 'Lisbon' for i in range(4, 9)), "Lisbon relatives not met"
        assert any(itinerary[i]['place'] == 'Porto' for i in range(15, 20)), "Porto conference not met"
        assert any(itinerary[i]['place'] == 'Warsaw' for i in range(19, 23)), "Warsaw friends not met"
        
        # Verify flight connections
        for i in range(25):
            current = itinerary[i]['place']
            next_ = itinerary[i+1]['place']
            if current != next_:
                assert (city_to_int[current], city_to_int[next_]) in allowed_transitions, \
                    f"No direct flight from {current} to {next_}"
        
        output = {"itinerary": itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))