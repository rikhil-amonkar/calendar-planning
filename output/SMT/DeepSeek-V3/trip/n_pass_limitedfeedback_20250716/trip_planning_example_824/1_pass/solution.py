import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Berlin', 'Split', 'Bucharest', 'Riga', 'Lisbon', 'Tallinn', 'Lyon']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: list of tuples (from, to)
    direct_flights = [
        ('Lisbon', 'Bucharest'), ('Bucharest', 'Lisbon'),
        ('Berlin', 'Lisbon'), ('Lisbon', 'Berlin'),
        ('Bucharest', 'Riga'), ('Riga', 'Bucharest'),
        ('Berlin', 'Riga'), ('Riga', 'Berlin'),
        ('Split', 'Lyon'), ('Lyon', 'Split'),
        ('Lisbon', 'Riga'), ('Riga', 'Lisbon'),
        ('Riga', 'Tallinn'), ('Tallinn', 'Riga'),
        ('Berlin', 'Split'), ('Split', 'Berlin'),
        ('Lyon', 'Lisbon'), ('Lisbon', 'Lyon'),
        ('Berlin', 'Tallinn'), ('Tallinn', 'Berlin'),
        ('Lyon', 'Bucharest'), ('Bucharest', 'Lyon')
    ]
    
    # Convert city names to indices in the flight list
    flight_pairs = [(city_map[fr], city_map[to]) for (fr, to) in direct_flights]
    
    # Duration requirements
    required_days = {
        'Berlin': 5,
        'Split': 3,
        'Bucharest': 3,
        'Riga': 5,
        'Lisbon': 3,
        'Tallinn': 4,
        'Lyon': 5
    }
    
    # Fixed events
    fixed_events = [
        (1, 5, 'Berlin'),   # Days 1-5 in Berlin
        (7, 11, 'Lyon'),     # Days 7-11 in Lyon
        (13, 15, 'Bucharest') # Days 13-15 in Bucharest
    ]
    
    # Create solver
    s = Solver()
    
    # Variables: day[i] is the city (index) on day i+1 (days are 1-based)
    days = [Int(f'day_{i+1}') for i in range(22)]
    
    # Each day's assignment is a city index (0 to 6)
    for day in days:
        s.add(day >= 0, day < 7)
    
    # Fixed events
    for (start, end, city) in fixed_events:
        city_idx = city_map[city]
        for day in range(start, end + 1):
            s.add(days[day - 1] == city_idx)
    
    # Duration constraints: count occurrences of each city
    for city in cities:
        city_idx = city_map[city]
        # Sum of days where city is present
        total = Sum([If(days[i] == city_idx, 1, 0) for i in range(22)])
        s.add(total == required_days[city])
    
    # Flight constraints: consecutive days in different cities must have a direct flight
    for i in range(21):
        current_day = days[i]
        next_day = days[i + 1]
        # If different cities, then there must be a direct flight
        s.add(Implies(current_day != next_day, 
                      Or([And(current_day == fr, next_day == to) for (fr, to) in flight_pairs])))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(22):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = cities[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        
        # Convert to the required JSON format
        result = {'itinerary': itinerary}
        return result
    else:
        return None

# Solve and print the itinerary
itinerary = solve_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print("No valid itinerary found.")