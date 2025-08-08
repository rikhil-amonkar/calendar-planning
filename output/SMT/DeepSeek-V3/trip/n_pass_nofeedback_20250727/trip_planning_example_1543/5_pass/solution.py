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
    
    # Duration constraints for all cities
    for city, days in cities.items():
        s.add(Sum([If(day_vars[i] == city_to_int[city], 1, 0) for i in range(26)]) == days)
    
    # Fixed constraints with flexibility
    # Prague: must be visited for 3 days including at least one day between 1-3
    s.add(Or([day_vars[i] == city_to_int['Prague'] for i in range(0, 3)]))
    
    # London: must be visited for 3 days including at least one day between 3-5
    s.add(Or([day_vars[i] == city_to_int['London'] for i in range(2, 5)]))
    
    # Lisbon: must be visited for 5 days including at least one day between 5-9
    s.add(Or([day_vars[i] == city_to_int['Lisbon'] for i in range(4, 9)]))
    
    # Porto: must be visited for 5 days including at least one day between 16-20
    s.add(Or([day_vars[i] == city_to_int['Porto'] for i in range(15, 20)]))
    
    # Warsaw: must be visited for 4 days including at least one day between 20-23
    s.add(Or([day_vars[i] == city_to_int['Warsaw'] for i in range(19, 23)]))
    
    # Flight transitions
    for i in range(25):
        current = day_vars[i]
        next_ = day_vars[i+1]
        s.add(Or(
            current == next_,
            And(current != next_, (current, next_) in allowed_transitions)
        ))
    
    # Additional constraints to help guide the solver
    # Ensure at least one transition day for overlapping constraints
    s.add(Or(
        day_vars[2] != day_vars[3],  # Day 3-4 transition
        day_vars[4] != day_vars[5],  # Day 5-6 transition
        day_vars[14] != day_vars[15], # Day 15-16 transition
        day_vars[19] != day_vars[20]  # Day 20-21 transition
    ))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 27):
            city_idx = model.evaluate(day_vars[day-1]).as_long()
            itinerary.append({"day": day, "place": int_to_city[city_idx]})
        
        # Verification
        day_counts = {city: 0 for city in city_list}
        for entry in itinerary:
            day_counts[entry['place']] += 1
        
        for city, days in cities.items():
            assert day_counts[city] == days, f"{city} duration mismatch"
        
        assert any(itinerary[i]['place'] == 'Prague' for i in range(0, 3)), "Prague workshop not met"
        assert any(itinerary[i]['place'] == 'London' for i in range(2, 5)), "London wedding not met"
        assert any(itinerary[i]['place'] == 'Lisbon' for i in range(4, 9)), "Lisbon relatives not met"
        assert any(itinerary[i]['place'] == 'Porto' for i in range(15, 20)), "Porto conference not met"
        assert any(itinerary[i]['place'] == 'Warsaw' for i in range(19, 23)), "Warsaw friends not met"
        
        for i in range(25):
            current = itinerary[i]['place']
            next_ = itinerary[i+1]['place']
            if current != next_:
                assert (city_to_int[current], city_to_int[next_]) in allowed_transitions, \
                    f"No direct flight from {current} to {next_}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))