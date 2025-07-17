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
    
    # Create Z3 variables: for each day, the city we're in (start and end)
    # day_start_city[d] is the city at the start of day d (1-based)
    day_start_city = [Int(f'day_{d}_start') for d in range(1, total_days + 1)]
    # day_end_city[d] is the city at the end of day d (1-based)
    day_end_city = [Int(f'day_{d}_end') for d in range(1, total_days + 1)]
    
    s = Solver()
    
    # Constraints for each day: start and end cities must be valid (0..4)
    for d in range(total_days):
        s.add(day_start_city[d] >= 0, day_start_city[d] < len(cities))
        s.add(day_end_city[d] >= 0, day_end_city[d] < len(cities))
    
    # For each day, if start and end cities are different, it's a flight day.
    # The flight must be a direct flight.
    for d in range(total_days):
        start_city = day_start_city[d]
        end_city = day_end_city[d]
        # If start != end, then the cities must be adjacent
        s.add(Implies(start_city != end_city, 
                      Or([And(start_city == city_to_idx[a], end_city == city_to_idx[b]) 
                          for a in adjacency for b in adjacency[a] if b in adjacency[a]])))
    
    # The start city of day d+1 is the end city of day d
    for d in range(total_days - 1):
        s.add(day_start_city[d+1] == day_end_city[d])
    
    # Geneva days 1-7: must be in Geneva at least those days.
    # So for days 1-7, Geneva must be either start or end city (or both).
    for d in range(7):  # days 1-7 (0-based 0-6)
        s.add(Or(day_start_city[d] == city_to_idx['Geneva'], day_end_city[d] == city_to_idx['Geneva']))
    
    # Oslo must be visited between day 19-23 (1-based days 19-23; 0-based 18-22)
    # At least one of start or end city is Oslo on these days.
    for d in range(18, 23):  # 0-based days 18-22
        s.add(Or(day_start_city[d] == city_to_idx['Oslo'], day_end_city[d] == city_to_idx['Oslo']))
    
    # Total days per city:
    # For each city, count the number of days where it's either start or end.
    def count_days(city):
        idx = city_to_idx[city]
        return Sum([If(Or(day_start_city[d] == idx, day_end_city[d] == idx), 1, 0) 
                   for d in range(total_days)])
    
    s.add(count_days('Paris') == 6)
    s.add(count_days('Oslo') == 5)
    s.add(count_days('Porto') == 7)
    s.add(count_days('Geneva') == 7)
    s.add(count_days('Reykjavik') == 2)
    
    # Initial city is Geneva on day 1 start.
    s.add(day_start_city[0] == city_to_idx['Geneva'])
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in range(total_days):
            start_day = d + 1  # 1-based
            start_city = cities[m.evaluate(day_start_city[d]).as_long()]
            end_city = cities[m.evaluate(day_end_city[d]).as_long()]
            if start_city == end_city:
                itinerary.append({'day': start_day, 'place': start_city})
            else:
                itinerary.append({'day': start_day, 'place': f"{start_city}/{end_city}"})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))