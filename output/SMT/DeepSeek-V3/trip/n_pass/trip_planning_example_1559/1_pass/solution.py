from z3 import *
import json

def solve_itinerary():
    # Cities to visit
    cities = ['Valencia', 'Oslo', 'Lyon', 'Prague', 'Paris', 'Nice', 'Seville', 'Tallinn', 'Mykonos', 'Lisbon']
    
    # Direct flights as adjacency list
    direct_flights = {
        'Lisbon': ['Paris', 'Seville', 'Prague', 'Valencia', 'Nice', 'Oslo', 'Lyon'],
        'Lyon': ['Nice', 'Prague', 'Paris', 'Valencia', 'Oslo', 'Lisbon'],
        'Nice': ['Lyon', 'Oslo', 'Mykonos', 'Paris', 'Lisbon'],
        'Oslo': ['Tallinn', 'Paris', 'Nice', 'Prague', 'Lyon', 'Lisbon'],
        'Paris': ['Lisbon', 'Oslo', 'Valencia', 'Nice', 'Lyon', 'Prague', 'Seville', 'Tallinn'],
        'Prague': ['Lyon', 'Lisbon', 'Oslo', 'Paris', 'Valencia', 'Tallinn'],
        'Seville': ['Lisbon', 'Paris', 'Valencia'],
        'Tallinn': ['Oslo', 'Paris', 'Prague'],
        'Valencia': ['Paris', 'Lisbon', 'Lyon', 'Seville', 'Prague'],
        'Mykonos': ['Nice'],
        'Lisbon': ['Paris', 'Seville', 'Prague', 'Valencia', 'Nice', 'Oslo', 'Lyon']  # Corrected name
    }
    
    # Correcting city name discrepancies (e.g., 'Lisbon' vs 'Lisbon')
    # Assuming 'Lisbon' is the correct name
    direct_flights['Lisbon'] = direct_flights.pop('Lisbon', direct_flights['Lisbon'])
    
    # Required days in each city
    required_days = {
        'Valencia': 2,
        'Oslo': 3,
        'Lyon': 4,
        'Prague': 3,
        'Paris': 4,
        'Nice': 4,
        'Seville': 5,
        'Tallinn': 2,
        'Mykonos': 5,
        'Lisbon': 2
    }
    required_days['Lisbon'] = 2  # Correcting key
    
    # Specific constraints
    # Valencia: friends between day 3 and 4. So Valencia must include day 3 or 4.
    # Oslo: friend between day 13-15. So Oslo must include one of these days.
    # Seville: annual show day 5-9. So Seville must include these days.
    # Mykonos: wedding day 21-25. So Mykonos must include these days.
    
    # Create a Z3 solver instance
    s = Solver()
    
    # Variables: itinerary[day] = city for each day 1..25
    itinerary = [Int(f'day_{i}') for i in range(1, 26)]
    
    # Assign each day to a city (represented by indices)
    city_indices = {city: idx for idx, city in enumerate(cities)}
    idx_to_city = {idx: city for city, idx in city_indices.items()}
    
    # Constraint: each day's value is a city index (0..9)
    for day in itinerary:
        s.add(day >= 0, day < len(cities))
    
    # Constraint: consecutive cities must have a direct flight
    for i in range(24):
        current_city = itinerary[i]
        next_city = itinerary[i+1]
        # For each possible pair, if they are not connected, then current_city != next_city is not sufficient.
        # Instead, we need to imply that if current_city is A, then next_city is in the adjacency list of A.
        # So for each city A, if current_city is A, then next_city is in direct_flights[A].
        constraints = []
        for city in cities:
            adj_list = direct_flights.get(city, [])
            adj_indices = [city_indices[c] for c in adj_list if c in city_indices]
            if adj_indices:
                s.add(Implies(current_city == city_indices[city], Or([next_city == idx for idx in adj_indices])))
            else:
                # No adjacent cities? Then this city can't be in the itinerary if followed by another city.
                pass
    
    # Constraint: total days per city must match required_days
    for city in cities:
        count = Sum([If(itinerary[i] == city_indices[city], 1, 0) for i in range(25)])
        s.add(count == required_days[city])
    
    # Specific constraints:
    # Valencia must include day 3 or 4.
    s.add(Or(itinerary[2] == city_indices['Valencia'], itinerary[3] == city_indices['Valencia']))
    
    # Oslo must include day 13, 14, or 15 (indices 12, 13, 14)
    s.add(Or(itinerary[12] == city_indices['Oslo'], itinerary[13] == city_indices['Oslo'], itinerary[14] == city_indices['Oslo']))
    
    # Seville must include days 5-9 (indices 4 to 8)
    for i in range(4, 9):
        s.add(itinerary[i] == city_indices['Seville'])
    
    # Mykonos must include days 21-25 (indices 20 to 24)
    for i in range(20, 25):
        s.add(itinerary[i] == city_indices['Mykonos'])
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        # Decode the itinerary
        itinerary_result = []
        for i in range(25):
            day = i + 1
            city_idx = model.evaluate(itinerary[i]).as_long()
            city = idx_to_city[city_idx]
            itinerary_result.append({"day": day, "place": city})
        
        # Verify the total days per city
        city_days = {city: 0 for city in cities}
        for entry in itinerary_result:
            city_days[entry['place']] += 1
        
        # Check if all required days are met
        for city in cities:
            assert city_days[city] == required_days[city], f"City {city} has {city_days[city]} days instead of {required_days[city]}"
        
        # Verify direct flights between consecutive cities
        for i in range(24):
            current_city = itinerary_result[i]['place']
            next_city = itinerary_result[i+1]['place']
            assert next_city in direct_flights[current_city], f"No direct flight from {current_city} to {next_city} on day {i+1}"
        
        # Verify specific constraints
        valencia_days = [entry['day'] for entry in itinerary_result if entry['place'] == 'Valencia']
        assert any(3 <= day <= 4 for day in valencia_days), "Valencia friends constraint not met"
        
        oslo_days = [entry['day'] for entry in itinerary_result if entry['place'] == 'Oslo']
        assert any(13 <= day <= 15 for day in oslo_days), "Oslo friend constraint not met"
        
        seville_days = [entry['day'] for entry in itinerary_result if entry['place'] == 'Seville']
        assert all(5 <= day <= 9 for day in seville_days), "Seville show constraint not met"
        
        mykonos_days = [entry['day'] for entry in itinerary_result if entry['place'] == 'Mykonos']
        assert all(21 <= day <= 25 for day in mykonos_days), "Mykonos wedding constraint not met"
        
        # Prepare the output
        output = {"itinerary": itinerary_result}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Fixing the direct_flights variable name (from direct_flights to direct_flights)
direct_flights = {
    'Lisbon': ['Paris', 'Seville', 'Prague', 'Valencia', 'Nice', 'Oslo', 'Lyon'],
    'Lyon': ['Nice', 'Prague', 'Paris', 'Valencia', 'Oslo', 'Lisbon'],
    'Nice': ['Lyon', 'Oslo', 'Mykonos', 'Paris', 'Lisbon'],
    'Oslo': ['Tallinn', 'Paris', 'Nice', 'Prague', 'Lyon', 'Lisbon'],
    'Paris': ['Lisbon', 'Oslo', 'Valencia', 'Nice', 'Lyon', 'Prague', 'Seville', 'Tallinn'],
    'Prague': ['Lyon', 'Lisbon', 'Oslo', 'Paris', 'Valencia', 'Tallinn'],
    'Seville': ['Lisbon', 'Paris', 'Valencia'],
    'Tallinn': ['Oslo', 'Paris', 'Prague'],
    'Valencia': ['Paris', 'Lisbon', 'Lyon', 'Seville', 'Prague'],
    'Mykonos': ['Nice']
}

# Correcting the function's use of direct_flights
def solve_itinerary_corrected():
    cities = ['Valencia', 'Oslo', 'Lyon', 'Prague', 'Paris', 'Nice', 'Seville', 'Tallinn', 'Mykonos', 'Lisbon']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    idx_to_city = {idx: city for idx, city in enumerate(cities)}
    
    required_days = {
        'Valencia': 2,
        'Oslo': 3,
        'Lyon': 4,
        'Prague': 3,
        'Paris': 4,
        'Nice': 4,
        'Seville': 5,
        'Tallinn': 2,
        'Mykonos': 5,
        'Lisbon': 2
    }
    
    s = Solver()
    itinerary = [Int(f'day_{i}') for i in range(1, 26)]
    
    for day in itinerary:
        s.add(day >= 0, day < len(cities))
    
    for i in range(24):
        current_city = itinerary[i]
        next_city = itinerary[i+1]
        constraints = []
        for city in cities:
            adj_cities = direct_flights.get(city, [])
            adj_indices = [city_indices[c] for c in adj_cities if c in city_indices]
            if adj_indices:
                s.add(Implies(current_city == city_indices[city], Or([next_city == adj_idx for adj_idx in adj_indices])))
    
    for city in cities:
        s.add(Sum([If(itinerary[i] == city_indices[city], 1, 0) for i in range(25)]) == required_days[city])
    
    # Valencia: friends between day 3-4 (indices 2-3)
    s.add(Or(itinerary[2] == city_indices['Valencia'], itinerary[3] == city_indices['Valencia']))
    
    # Oslo: friend between day 13-15 (indices 12-14)
    s.add(Or(
        itinerary[12] == city_indices['Oslo'],
        itinerary[13] == city_indices['Oslo'],
        itinerary[14] == city_indices['Oslo']
    ))
    
    # Seville: days 5-9 (indices 4-8)
    for i in range(4, 9):
        s.add(itinerary[i] == city_indices['Seville'])
    
    # Mykonos: days 21-25 (indices 20-24)
    for i in range(20, 25):
        s.add(itinerary[i] == city_indices['Mykonos'])
    
    if s.check() == sat:
        model = s.model()
        itinerary_result = []
        for i in range(25):
            day = i + 1
            city_idx = model.evaluate(itinerary[i]).as_long()
            city = idx_to_city[city_idx]
            itinerary_result.append({"day": day, "place": city})
        
        output = {"itinerary": itinerary_result}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Execute the corrected function
result = solve_itinerary_corrected()
print(json.dumps(result, indent=2))