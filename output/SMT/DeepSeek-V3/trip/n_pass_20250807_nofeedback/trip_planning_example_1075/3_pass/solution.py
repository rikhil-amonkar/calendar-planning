from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Vienna', 'Lyon', 'Edinburgh', 'Reykjavik', 'Stuttgart', 'Manchester', 'Split', 'Prague']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Reykjavik': ['Stuttgart', 'Vienna'],
        'Stuttgart': ['Split', 'Vienna', 'Edinburgh', 'Manchester'],
        'Prague': ['Manchester', 'Edinburgh', 'Vienna', 'Split', 'Lyon', 'Reykjavik'],
        'Edinburgh': ['Prague', 'Stuttgart'],
        'Manchester': ['Split', 'Prague', 'Vienna'],
        'Vienna': ['Manchester', 'Lyon', 'Split', 'Prague', 'Stuttgart', 'Reykjavik'],
        'Split': ['Lyon', 'Manchester', 'Prague', 'Vienna', 'Stuttgart'],
        'Lyon': ['Vienna', 'Split', 'Prague']
    }
    
    # Required days per city
    required_days = {
        'Vienna': 4,
        'Lyon': 3,
        'Edinburgh': 4,
        'Reykjavik': 5,
        'Stuttgart': 5,
        'Manchester': 2,
        'Split': 5,
        'Prague': 4
    }
    
    # Special constraints
    # Edinburgh must be visited from day 5 to 8 (inclusive)
    # Split must include days 19-23 (wedding)
    
    # Initialize Z3 solver
    s = Solver()
    
    # Variables: day[i] is the city visited on day i (1-based)
    days = [Int(f'day_{i}') for i in range(1, 26)]  # days 1 to 25
    
    # Each day must be a valid city index (0 to 7)
    for day in days:
        s.add(And(day >= 0, day < len(cities)))
    
    # Edinburgh from day 5 to 8
    for i in range(5, 9):
        s.add(days[i-1] == city_map['Edinburgh'])
    
    # Split must include days 19-23 (wedding)
    for i in range(19, 24):
        s.add(days[i-1] == city_map['Split'])
    
    # Transition constraints: consecutive days must be the same or have a direct flight
    for i in range(1, 25):
        current_city = days[i-1]
        next_city = days[i]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_map[city], next_city == city_map[neighbor])
              for city, neighbors in direct_flights.items()
              for neighbor in neighbors]
        ))
    
    # Total days per city
    for city, req in required_days.items():
        idx = city_map[city]
        total = Sum([If(days[i] == idx, 1, 0) for i in range(25)])
        s.add(total == req)
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(1, 26):
            city_idx = m.evaluate(days[i-1]).as_long()
            itinerary.append({'day': i, 'place': cities[city_idx]})
        
        # Verify the itinerary meets all constraints
        # (This is a sanity check; Z3 should have ensured correctness)
        return {'itinerary': itinerary}
    else:
        return None

# Generate and print the itinerary
itinerary = solve_itinerary()
if itinerary:
    print(itinerary)
else:
    print("No valid itinerary found.")