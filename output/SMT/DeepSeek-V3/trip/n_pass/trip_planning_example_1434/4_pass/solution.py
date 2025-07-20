from z3 import *

def solve_itinerary():
    # Cities
    cities = {
        'Rome': 0,
        'Mykonos': 1,
        'Lisbon': 2,
        'Frankfurt': 3,
        'Nice': 4,
        'Stuttgart': 5,
        'Venice': 6,
        'Dublin': 7,
        'Bucharest': 8,
        'Seville': 9
    }
    inv_cities = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [5, 6, 1, 9, 7, 8, 2],  # Rome
        1: [0, 4],                   # Mykonos
        2: [9, 8, 6, 7, 5, 0, 3],    # Lisbon
        3: [6, 0, 5, 8, 7, 2, 4],    # Frankfurt
        4: [1, 6, 7, 0, 2],          # Nice
        5: [0, 6, 3, 2],             # Stuttgart
        6: [0, 3, 5, 2, 4, 7],       # Venice
        7: [8, 2, 6, 0, 4, 9],       # Dublin
        8: [7, 2, 0, 3],             # Bucharest
        9: [2, 7, 0]                 # Seville
    }
    
    # Duration constraints
    durations = {
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
    
    # Event constraints
    # Frankfurt between day 1 and 5 (inclusive) for wedding
    # Mykonos between day 10 and 11 (inclusive) to meet friends
    # Seville between day 13 and 17 (inclusive) for conference
    
    # Create Z3 variables: day[i] is the city on day i+1 (since days are 1-based)
    days = [Int(f'day_{i+1}') for i in range(23)]
    
    s = Solver()
    
    # Each day is a city (0..9)
    for d in days:
        s.add(And(d >= 0, d <= 9))
    
    # Duration constraints: count occurrences of each city in days
    for city, cid in cities.items():
        total = durations[city]
        s.add(Sum([If(d == cid, 1, 0) for d in days]) == total)
    
    # Frankfurt between day 1 and 5 (days 0..4 in zero-based)
    for i in range(5):
        s.add(days[i] == cities['Frankfurt'])
    
    # Mykonos on day 10 or 11 (days 9 or 10 in zero-based)
    s.add(Or(days[9] == cities['Mykonos'], days[10] == cities['Mykonos']))
    
    # Seville between day 13 and 17 (days 12..16 in zero-based)
    for i in range(12, 17):
        s.add(days[i] == cities['Seville'])
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(22):
        current_city = days[i]
        next_city = days[i+1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            And(current_city != next_city, Or([next_city == c for c in direct_flights[current_city.as_long() if isinstance(current_city, IntNumRef) else current_city]]))
        ))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(23):
            cid = m[days[i]].as_long()
            city = inv_cities[cid]
            itinerary.append({'day': i+1, 'place': city})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Generate and print the itinerary
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))