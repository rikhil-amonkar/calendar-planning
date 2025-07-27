from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Oslo', 'Helsinki', 'Edinburgh', 'Riga', 'Tallinn', 'Budapest', 'Vilnius', 'Porto', 'Geneva']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional unless specified)
    direct_flights = [
        ('Porto', 'Oslo'),
        ('Edinburgh', 'Budapest'),
        ('Edinburgh', 'Geneva'),
        ('Riga', 'Tallinn'),
        ('Edinburgh', 'Porto'),
        ('Vilnius', 'Helsinki'),
        ('Tallinn', 'Vilnius'),
        ('Riga', 'Oslo'),
        ('Geneva', 'Oslo'),
        ('Edinburgh', 'Oslo'),
        ('Edinburgh', 'Helsinki'),
        ('Vilnius', 'Oslo'),
        ('Riga', 'Helsinki'),
        ('Budapest', 'Geneva'),
        ('Helsinki', 'Budapest'),
        ('Helsinki', 'Oslo'),
        ('Edinburgh', 'Riga'),
        ('Tallinn', 'Helsinki'),
        ('Geneva', 'Porto'),
        ('Budapest', 'Oslo'),
        ('Helsinki', 'Geneva'),
        ('Riga', 'Vilnius'),
        ('Tallinn', 'Oslo')
    ]
    
    # Make sure flights are bidirectional
    bidirectional_flights = set()
    for a, b in direct_flights:
        bidirectional_flights.add((a, b))
        bidirectional_flights.add((b, a))
    direct_flights = bidirectional_flights
    
    # Required days in each city
    required_days = {
        'Oslo': 2,
        'Helsinki': 2,
        'Edinburgh': 3,
        'Riga': 2,
        'Tallinn': 5,
        'Budapest': 5,
        'Vilnius': 5,
        'Porto': 5,
        'Geneva': 4
    }
    
    # Create Z3 variables: itinerary[d] is the city on day d (1-based)
    itinerary = [Int(f'day_{i}') for i in range(1, 26)]  # days 1 to 25
    
    s = Solver()
    
    # Each day must be a valid city index (0 to 8)
    for day in itinerary:
        s.add(day >= 0, day < len(cities))
    
    # Constraints for transitions between days: consecutive days must be same city or have a direct flight
    for i in range(24):  # days 1..24 and 2..25
        current_city = itinerary[i]
        next_city = itinerary[i+1]
        # Either stay in the same city or take a direct flight
        s.add(Or(
            current_city == next_city,
            Or([And(current_city == city_to_idx[a], next_city == city_to_idx[b]) 
                for a, b in direct_flights])
        ))
    
    # Count the number of days spent in each city
    city_days = {city: 0 for city in cities}
    for city_idx, city in enumerate(cities):
        city_days[city] = Sum([If(itinerary[d] == city_idx, 1, 0) for d in range(25)])
    
    # Add constraints for required days in each city
    for city, days in required_days.items():
        s.add(city_days[city] == days)
    
    # Special constraints:
    # 1. Wedding in Tallinn between day 4 and day 8 (i.e., at least one day in Tallinn in days 4-8)
    s.add(Or([itinerary[d] == city_to_idx['Tallinn'] for d in range(3, 8)]))  # days 4-8 (0-based 3-7)
    
    # 2. Meet friend in Oslo between day 24 and 25 (so Oslo must be on day 24 or 25)
    s.add(Or(
        itinerary[23] == city_to_idx['Oslo'],  # day 24 (0-based 23)
        itinerary[24] == city_to_idx['Oslo']   # day 25 (0-based 24)
    ))
    
    # Try to find a solution
    if s.check() == sat:
        m = s.model()
        itinerary_result = []
        for day in range(25):
            city_idx = m.evaluate(itinerary[day]).as_long()
            itinerary_result.append({
                'day': day + 1,
                'city': cities[city_idx]
            })
        
        # Convert to the required JSON format
        json_output = {
            'itinerary': itinerary_result
        }
        return json_output
    else:
        return None

# Solve and print the itinerary
itinerary = solve_itinerary()
if itinerary:
    print(itinerary)
else:
    print("No valid itinerary found.")