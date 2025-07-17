from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Prague', 'Frankfurt', 'Naples', 'Helsinki', 'Lyon']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (undirected)
    direct_flights = [
        ('Prague', 'Lyon'),
        ('Prague', 'Frankfurt'),
        ('Frankfurt', 'Lyon'),
        ('Helsinki', 'Naples'),
        ('Helsinki', 'Frankfurt'),
        ('Naples', 'Frankfurt'),
        ('Prague', 'Helsinki')
    ]
    # Correcting the typo in the original flight list
    direct_flights = [
        (a, b) if b != 'Helsinki' else (a, 'Helsinki') for a, b in direct_flights
    ]
    # Create a set of possible direct flights
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Total days
    total_days = 12
    
    # Create Z3 variables for each day: which city is visited on that day
    day_city = [Int(f'day_{day}_city') for day in range(1, total_days + 1)]
    
    s = Solver()
    
    # Each day_city variable must be between 0 and 4 (indices of cities)
    for day in range(total_days):
        s.add(day_city[day] >= 0, day_city[day] < len(cities))
    
    # Constraints for transitions: consecutive days must be either same city or connected by a direct flight
    for day in range(total_days - 1):
        current_city = day_city[day]
        next_city = day_city[day + 1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            *[
                And(current_city == city_indices[a], next_city == city_indices[b])
                for a, b in flight_pairs
            ]
        ))
    
    # Count days per city
    city_days = [0] * len(cities)
    for city_idx in range(len(cities)):
        city_days[city_idx] = Sum([If(day_city[day] == city_idx, 1, 0) for day in range(total_days)])
    
    # Required days per city
    s.add(city_days[city_indices['Frankfurt']] == 3)
    s.add(city_days[city_indices['Naples']] == 4)
    s.add(city_days[city_indices['Helsinki']] == 4)
    s.add(city_days[city_indices['Lyon']] == 3)
    s.add(city_days[city_indices['Prague']] == 2)
    
    # Helsinki must be visited from day 2 to day 5 (days 2,3,4,5 in 1-based)
    for day in [1, 2, 3, 4]:  # 0-based days 1 to 4 (2-5 in 1-based)
        s.add(day_city[day] == city_indices['Helsinki'])
    
    # Workshop in Prague between day 1 and day 2: so must be in Prague on day 0 (1-based day 1) or day 1 (1-based day 2)
    # Assuming the workshop is on day 1 (1-based), which is index 0
    s.add(day_city[0] == city_indices['Prague'])
    
    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(total_days):
            city_idx = m.evaluate(day_city[day]).as_long()
            itinerary.append({'day': day + 1, 'place': cities[city_idx]})
        
        # Verify the solution meets all constraints
        # Check city days
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_counts[entry['place']] += 1
        
        assert city_counts['Frankfurt'] == 3
        assert city_counts['Naples'] == 4
        assert city_counts['Helsinki'] == 4
        assert city_counts['Lyon'] == 3
        assert city_counts['Prague'] == 2
        
        # Check Helsinki days 2-5 (1-based) are Helsinki
        for day in [1, 2, 3, 4]:  # 0-based days for 2-5 in 1-based)
            assert itinerary[day]['place'] == 'Helsinki'
        
        # Check Prague on day 1 (1-based is index 0)
        assert itinerary[0]['place'] == 'Prague'
        
        # Check flight transitions are valid
        for day in range(total_days - 1):
            current_place = itinerary[day]['place']
            next_place = itinerary[day + 1]['place']
            if current_place != next_place:
                assert (current_place, next_place) in flight_pairs
        
        # Generate the JSON output
        output = {
            'itinerary': [
                {'day': entry['day'], 'place': entry['place']}
                for entry in itinerary
            ]
        }
        return output
    else:
        return {"error": "No valid itinerary found"}

# Call the function and print the result
import json
result = solve_itinerary()
print(json.dumps(result, indent=2))