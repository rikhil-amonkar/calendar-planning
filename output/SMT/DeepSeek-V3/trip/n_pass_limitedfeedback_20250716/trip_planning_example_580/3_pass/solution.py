from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Geneva', 'Paris', 'Oslo', 'Porto', 'Reykjavik']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    adjacency = {
        'Paris': ['Oslo', 'Geneva', 'Porto', 'Reykjavik'],
        'Oslo': ['Paris', 'Geneva', 'Reykjavik', 'Porto'],
        'Geneva': ['Oslo', 'Paris', 'Porto'],
        'Porto': ['Paris', 'Geneva', 'Oslo'],
        'Reykjavik': ['Paris', 'Oslo']
    }
    
    # Total days
    total_days = 23
    
    # Create Z3 variables: for each day, the city we're in
    day_city = [Int(f'day_{d}_city') for d in range(total_days)]
    
    s = Solver()
    
    # Constraints for each day: city must be valid (0..4)
    for d in range(total_days):
        s.add(day_city[d] >= 0, day_city[d] < len(cities))
    
    # Geneva must be visited on days 1-7 (0-based days 0-6)
    for d in range(7):
        s.add(day_city[d] == city_to_idx['Geneva'])
    
    # Oslo must be visited between days 19-23 (0-based days 18-22)
    for d in range(18, 23):
        s.add(day_city[d] == city_to_idx['Oslo'])
    
    # Total days per city
    def count_days(city):
        idx = city_to_idx[city]
        return Sum([If(day_city[d] == idx, 1, 0) for d in range(total_days)])
    
    s.add(count_days('Paris') == 6)
    s.add(count_days('Oslo') == 5)
    s.add(count_days('Porto') == 7)
    s.add(count_days('Geneva') == 7)
    s.add(count_days('Reykjavik') == 2)
    
    # Flight transitions: consecutive days must be the same or connected by a direct flight
    for d in range(total_days - 1):
        current_city = day_city[d]
        next_city = day_city[d + 1]
        s.add(Or(
            current_city == next_city,
            And(current_city == city_to_idx['Paris'], next_city == city_to_idx['Oslo']),
            And(current_city == city_to_idx['Paris'], next_city == city_to_idx['Geneva']),
            And(current_city == city_to_idx['Paris'], next_city == city_to_idx['Porto']),
            And(current_city == city_to_idx['Paris'], next_city == city_to_idx['Reykjavik']),
            And(current_city == city_to_idx['Oslo'], next_city == city_to_idx['Paris']),
            And(current_city == city_to_idx['Oslo'], next_city == city_to_idx['Geneva']),
            And(current_city == city_to_idx['Oslo'], next_city == city_to_idx['Reykjavik']),
            And(current_city == city_to_idx['Oslo'], next_city == city_to_idx['Porto']),
            And(current_city == city_to_idx['Geneva'], next_city == city_to_idx['Oslo']),
            And(current_city == city_to_idx['Geneva'], next_city == city_to_idx['Paris']),
            And(current_city == city_to_idx['Geneva'], next_city == city_to_idx['Porto']),
            And(current_city == city_to_idx['Porto'], next_city == city_to_idx['Paris']),
            And(current_city == city_to_idx['Porto'], next_city == city_to_idx['Geneva']),
            And(current_city == city_to_idx['Porto'], next_city == city_to_idx['Oslo']),
            And(current_city == city_to_idx['Reykjavik'], next_city == city_to_idx['Paris']),
            And(current_city == city_to_idx['Reykjavik'], next_city == city_to_idx['Oslo'])
        ))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_place = cities[m.evaluate(day_city[0]).as_long()]
        start_day = 1
        for d in range(1, total_days):
            next_place = cities[m.evaluate(day_city[d]).as_long()]
            if next_place != current_place:
                itinerary.append({'day_range': f'Day {start_day}-{d}', 'place': current_place})
                itinerary.append({'day_range': f'Day {d+1}', 'place': f"{current_place}/{next_place}"})
                start_day = d + 1
                current_place = next_place
        itinerary.append({'day_range': f'Day {start_day}-{total_days}', 'place': current_place})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))