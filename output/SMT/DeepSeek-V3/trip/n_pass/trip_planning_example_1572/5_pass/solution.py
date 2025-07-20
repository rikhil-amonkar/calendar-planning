from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Lyon': 3,
        'Paris': 5,
        'Riga': 2,
        'Berlin': 2,
        'Stockholm': 3,
        'Zurich': 5,
        'Nice': 2,
        'Seville': 3,
        'Milan': 3,
        'Naples': 4
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ('Paris', 'Stockholm'),
        ('Seville', 'Paris'),
        ('Naples', 'Zurich'),
        ('Nice', 'Riga'),
        ('Berlin', 'Milan'),
        ('Paris', 'Zurich'),
        ('Paris', 'Nice'),
        ('Milan', 'Paris'),
        ('Milan', 'Riga'),
        ('Paris', 'Lyon'),
        ('Milan', 'Naples'),
        ('Paris', 'Riga'),
        ('Berlin', 'Stockholm'),
        ('Stockholm', 'Riga'),
        ('Nice', 'Zurich'),
        ('Milan', 'Zurich'),
        ('Lyon', 'Nice'),
        ('Zurich', 'Stockholm'),
        ('Zurich', 'Riga'),
        ('Berlin', 'Naples'),
        ('Milan', 'Stockholm'),
        ('Berlin', 'Zurich'),
        ('Milan', 'Seville'),
        ('Paris', 'Naples'),
        ('Berlin', 'Riga'),
        ('Nice', 'Stockholm'),
        ('Berlin', 'Paris'),
        ('Nice', 'Naples'),
        ('Berlin', 'Nice')
    ]
    
    # Create a set of all possible direct flights for quick lookup
    flight_set = set()
    for a, b in direct_flights:
        flight_set.add((a, b))
        flight_set.add((b, a))
    
    # Initialize Z3 solver
    s = Solver()
    
    # Create variables: day_1 to day_23, each can be one of the cities
    days = [Int(f'day_{i}') for i in range(1, 24)]  # days 1 to 23
    
    # Map each city to a unique integer
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Add constraints: each day's variable must be one of the city IDs
    for day in days:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Fixed events:
    # Berlin: wedding between day 1 and 2 (so day 1 and 2 are Berlin)
    s.add(days[0] == city_ids['Berlin'])  # day 1
    s.add(days[1] == city_ids['Berlin'])  # day 2
    
    # Nice: workshop between day 12 and 13 (so day 12 and 13 are Nice)
    s.add(days[11] == city_ids['Nice'])   # day 12
    s.add(days[12] == city_ids['Nice'])   # day 13
    
    # Stockholm: annual show from day 20 to 22 (so days 20, 21, 22)
    s.add(days[19] == city_ids['Stockholm'])  # day 20
    s.add(days[20] == city_ids['Stockholm'])  # day 21
    s.add(days[21] == city_ids['Stockholm'])  # day 22
    
    # Transition constraints: consecutive days must be the same city or have a direct flight
    for i in range(22):  # days 1..22 and 2..23
        day1 = days[i]
        day2 = days[i+1]
        # Either same city or connected by a direct flight
        s.add(Or(
            day1 == day2,
            *[
                And(day1 == city_ids[a], day2 == city_ids[b])
                for a, b in flight_set
            ]
        ))
    
    # Duration constraints: each city must be visited for exactly the specified number of days
    for city, required_days in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(day == city_id, 1, 0) for day in days]) == required_days)
    
    # Additional constraints to help guide the solver
    # Ensure we don't have too many single-day stays (except for transitions)
    for i in range(1, 22):
        s.add(Or(
            days[i-1] == days[i],  # Same city
            days[i] == days[i+1],  # Same city next day
            And(days[i-1] != days[i], days[i] != days[i+1])  # Transition day
        ))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 24):
            day_var = days[i-1]
            city_id = model[day_var].as_long()
            city = id_to_city[city_id]
            itinerary.append({'day': i, 'place': city})
        
        # Verify the solution meets all constraints (sanity check)
        # Check durations
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        for city, required in cities.items():
            assert city_days[city] == required, f"City {city} has {city_days[city]} days instead of {required}"
        
        # Check transitions
        for i in range(len(itinerary) - 1):
            current = itinerary[i]['place']
            next_ = itinerary[i+1]['place']
            if current != next_:
                assert (current, next_) in flight_set or (next_, current) in flight_set, f"No flight between {current} and {next_}"
        
        # Check fixed events
        assert itinerary[0]['place'] == 'Berlin' and itinerary[1]['place'] == 'Berlin', "Berlin wedding days incorrect"
        assert itinerary[11]['place'] == 'Nice' and itinerary[12]['place'] == 'Nice', "Nice workshop days incorrect"
        assert itinerary[19]['place'] == 'Stockholm' and itinerary[20]['place'] == 'Stockholm' and itinerary[21]['place'] == 'Stockholm', "Stockholm show days incorrect"
        
        return {'itinerary': itinerary}
    else:
        return None

# Solve and print the itinerary
result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found")