from z3 import *
import json

def solve_itinerary():
    # Cities to visit with their required days
    cities = {
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
    
    # Direct flight connections (bidirectional)
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

    # Create solver
    s = Solver()

    # Create variables for each day (1-25)
    days = [Int(f'day_{i}') for i in range(1, 26)]
    city_names = list(cities.keys())
    city_to_idx = {city: idx for idx, city in enumerate(city_names)}
    idx_to_city = {idx: city for idx, city in enumerate(city_names)}

    # Each day must be assigned to a valid city
    for day in days:
        s.add(day >= 0, day < len(city_names))

    # Flight constraints between consecutive days
    for i in range(24):
        current_city = days[i]
        next_city = days[i+1]
        possible_flights = []
        for city in city_names:
            adj_cities = direct_flights.get(city, [])
            adj_indices = [city_to_idx[c] for c in adj_cities if c in city_to_idx]
            possible_flights.append(And(current_city == city_to_idx[city], 
                                    Or([next_city == idx for idx in adj_indices])))
        s.add(Or(possible_flights))

    # Total days per city must match requirements
    for city, req_days in cities.items():
        count = Sum([If(days[i] == city_to_idx[city], 1, 0) for i in range(25)])
        s.add(count == req_days)

    # Specific constraints:
    # Valencia must be visited on day 3 or 4
    s.add(Or(days[2] == city_to_idx['Valencia'], days[3] == city_to_idx['Valencia']))

    # Oslo must be visited between days 13-15
    s.add(Or([days[i] == city_to_idx['Oslo'] for i in range(12, 15)]))

    # Seville must be visited from day 5 to 9 (inclusive)
    for i in range(4, 9):
        s.add(days[i] == city_to_idx['Seville'])

    # Mykonos must be visited from day 21 to 25 (inclusive)
    for i in range(20, 25):
        s.add(days[i] == city_to_idx['Mykonos'])

    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(25):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = idx_to_city[city_idx]
            itinerary.append({"day": day_num, "place": city})
        
        # Verify all constraints are satisfied
        city_counts = {city: 0 for city in city_names}
        for entry in itinerary:
            city_counts[entry['place']] += 1
        
        for city, count in city_counts.items():
            assert count == cities[city], f"City {city} has {count} days instead of {cities[city]}"
        
        for i in range(24):
            current = itinerary[i]['place']
            next_c = itinerary[i+1]['place']
            assert next_c in direct_flights[current], f"No flight from {current} to {next_c} on day {i+1}"
        
        # Verify specific constraints
        valencia_days = [e['day'] for e in itinerary if e['place'] == 'Valencia']
        assert any(3 <= d <= 4 for d in valencia_days), "Valencia constraint failed"
        
        oslo_days = [e['day'] for e in itinerary if e['place'] == 'Oslo']
        assert any(13 <= d <= 15 for d in oslo_days), "Oslo constraint failed"
        
        seville_days = [e['day'] for e in itinerary if e['place'] == 'Seville']
        assert all(5 <= d <= 9 for d in seville_days), "Seville constraint failed"
        
        mykonos_days = [e['day'] for e in itinerary if e['place'] == 'Mykonos']
        assert all(21 <= d <= 25 for d in mykonos_days), "Mykonos constraint failed"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Run the solver
result = solve_itinerary()
print(json.dumps(result, indent=2))