from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Frankfurt': 4,
        'Manchester': 4,
        'Valencia': 4,
        'Naples': 4,
        'Oslo': 3,
        'Vilnius': 2
    }
    
    # Direct flight connections
    connections = {
        'Valencia': ['Frankfurt', 'Naples'],
        'Manchester': ['Frankfurt', 'Naples', 'Oslo'],
        'Naples': ['Manchester', 'Frankfurt', 'Oslo', 'Valencia'],
        'Oslo': ['Naples', 'Frankfurt', 'Vilnius', 'Manchester'],
        'Vilnius': ['Frankfurt', 'Oslo'],
        'Frankfurt': ['Valencia', 'Manchester', 'Naples', 'Oslo', 'Vilnius']
    }
    
    # Create a Z3 solver instance
    s = Solver()
    
    # Create variables for each day (1-based)
    days = [Int(f'day_{i}') for i in range(1, 17)]
    
    # Assign each day to a city (represented by numbers)
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Add constraints: each day's variable must be one of the city IDs
    for day in days:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Fixed constraints:
    # Days 13-16 must be Frankfurt (city_ids['Frankfurt'])
    for day in days[12:16]:  # days[12] is day 13 (0-based)
        s.add(day == city_ids['Frankfurt'])
    
    # Day 12 must be Vilnius (since day 12-13 includes Vilnius, and day 13 is Frankfurt)
    s.add(days[11] == city_ids['Vilnius'])  # days[11] is day 12
    
    # Flight constraints: consecutive days must be connected
    for i in range(len(days) - 1):
        current_day = days[i]
        next_day = days[i + 1]
        # The constraint is that next_day must be in the connections of current_day's city
        s.add(Or([
            And(current_day == city_ids[city], 
                Or([next_day == city_ids[connected_city] for connected_city in connections[city]]))
            for city in cities
        ]))
    
    # Constraints for total days per city
    for city in cities:
        total_days = cities[city]
        # Count the number of days assigned to this city
        count = Sum([If(day == city_ids[city], 1, 0) for day in days])
        s.add(count == total_days)
    
    # Additional constraints to ensure the itinerary is feasible
    # Ensure that the first day is not Vilnius (since the wedding is on day 12)
    s.add(days[0] != city_ids['Vilnius'])
    
    # Ensure that the last day is Frankfurt (since days 13-16 are Frankfurt)
    s.add(days[15] == city_ids['Frankfurt'])
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(16):
            day_num = i + 1
            city_id = model.evaluate(days[i]).as_long()
            city = id_to_city[city_id]
            itinerary.append({'day': day_num, 'place': city})
        
        # Convert to the required JSON format
        result = {'itinerary': itinerary}
        return json.dumps(result, indent=2)
    else:
        return json.dumps({'error': 'No solution found'}, indent=2)

# Execute and print the result
print(solve_itinerary())