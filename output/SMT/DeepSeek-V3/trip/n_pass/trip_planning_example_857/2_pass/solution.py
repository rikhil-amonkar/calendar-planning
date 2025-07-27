import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Porto', 'Geneva', 'Mykonos', 'Manchester', 'Hamburg', 'Naples', 'Frankfurt']
    city_map = {city: idx for idx, city in enumerate(cities)}
    idx_to_city = {idx: city for city, idx in city_map.items()}
    
    # Direct flights: list of tuples (from, to)
    direct_flights = [
        ('Hamburg', 'Frankfurt'), ('Naples', 'Mykonos'), ('Hamburg', 'Porto'),
        ('Hamburg', 'Geneva'), ('Mykonos', 'Geneva'), ('Frankfurt', 'Geneva'),
        ('Frankfurt', 'Porto'), ('Geneva', 'Porto'), ('Geneva', 'Manchester'),
        ('Naples', 'Manchester'), ('Frankfurt', 'Naples'), ('Frankfurt', 'Manchester'),
        ('Naples', 'Geneva'), ('Porto', 'Manchester'), ('Hamburg', 'Manchester')
    ]
    # Make sure flights are bidirectional
    all_flights = set()
    for a, b in direct_flights:
        all_flights.add((a, b))
        all_flights.add((b, a))
    
    # Duration constraints
    durations = {
        'Porto': 2,
        'Geneva': 3,
        'Mykonos': 3,
        'Manchester': 4,
        'Hamburg': 5,
        'Naples': 5,
        'Frankfurt': 2
    }
    
    # Event constraints
    # Mykonos: friend visit between day 10-12 (inclusive)
    # Manchester: wedding between day 15-18 (inclusive)
    # Frankfurt: show on day 5-6
    
    # Z3 variables: day[i] is the city index for day i+1 (since days are 1-based)
    s = Solver()
    num_days = 18
    day = [Int(f"day_{i}") for i in range(num_days)]
    
    # Each day must be a valid city index (0 to 6)
    for d in day:
        s.add(And(d >= 0, d <= 6))
    
    # Duration constraints: count occurrences of each city
    for city, dur in durations.items():
        city_idx = city_map[city]
        s.add(Sum([If(day[i] == city_idx, 1, 0) for i in range(num_days)]) == dur)
    
    # Event constraints:
    # Frankfurt must include day 5 and 6 (0-based: days 4 and 5)
    s.add(day[4] == city_map['Frankfurt'])
    s.add(day[5] == city_map['Frankfurt'])
    
    # Mykonos must include at least one day between 10-12 (1-based: days 9,10,11 0-based)
    s.add(Or(day[9] == city_map['Mykonos'], day[10] == city_map['Mykonos'], day[11] == city_map['Mykonos']))
    
    # Manchester must include at least one day between 15-18 (1-based: days 14-17 0-based)
    s.add(Or([day[i] == city_map['Manchester'] for i in range(14, 18)]))
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(num_days - 1):
        current_city_idx = day[i]
        next_city_idx = day[i+1]
        # Either same city or connected by a direct flight
        same_city = (current_city_idx == next_city_idx)
        flight_possible = Or([And(current_city_idx == city_map[a], next_city_idx == city_map[b]) for a, b in all_flights])
        s.add(Or(same_city, flight_possible))
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(num_days):
            city_idx = m.evaluate(day[i]).as_long()
            itinerary.append({"day": i+1, "place": idx_to_city[city_idx]})
        
        # Verify durations
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_counts[entry['place']] += 1
        for city, dur in durations.items():
            assert city_counts[city] == dur, f"Duration mismatch for {city}: expected {dur}, got {city_counts[city]}"
        
        # Verify flights
        for i in range(num_days - 1):
            current_place = itinerary[i]['place']
            next_place = itinerary[i+1]['place']
            if current_place != next_place:
                assert (current_place, next_place) in all_flights or (next_place, current_place) in all_flights, \
                    f"No direct flight between {current_place} and {next_place} on day {i+1}"
        
        # Verify events
        # Frankfurt on days 5-6 (1-based)
        assert itinerary[4]['place'] == 'Frankfurt' and itinerary[5]['place'] == 'Frankfurt', "Frankfurt show not on days 5-6"
        # Mykonos between days 10-12 (1-based days 10,11,12)
        mykonos_days = [entry['day'] for entry in itinerary if entry['place'] == 'Mykonos']
        assert any(10 <= day <= 12 for day in mykonos_days), "Mykonos friend visit not between days 10-12"
        # Manchester wedding between days 15-18
        manchester_days = [entry['day'] for entry in itinerary if entry['place'] == 'Manchester']
        assert any(15 <= day <= 18 for day in manchester_days), "Manchester wedding not between days 15-18"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))