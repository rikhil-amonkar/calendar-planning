from z3 import *
import json

def main():
    # Cities and their required days
    cities = ['Seville', 'Stuttgart', 'Porto', 'Madrid']
    req_days = {'Seville': 2, 'Stuttgart': 7, 'Porto': 3, 'Madrid': 4}
    
    # Direct flights (bidirectional)
    direct_flights = [('Porto', 'Stuttgart'), ('Seville', 'Porto'), 
                     ('Madrid', 'Porto'), ('Madrid', 'Seville')]
    
    # Initialize solver
    s = Solver()
    
    # Variables for each city: start day, end day, and order in itinerary
    start = {city: Int(f'start_{city}') for city in cities}
    end = {city: Int(f'end_{city}') for city in cities}
    order = {city: Int(f'order_{city}') for city in cities}
    
    # Constraints for each city
    for city in cities:
        s.add(start[city] >= 1, start[city] <= 13)
        s.add(end[city] >= 1, end[city] <= 13)
        s.add(start[city] <= end[city])
        s.add(end[city] - start[city] + 1 == req_days[city])
        s.add(order[city] >= 0, order[city] <= 3)
    
    # Order must be a permutation
    s.add(Distinct([order[city] for city in cities]))
    
    # First city starts on day 1, last city ends on day 13
    first_city = [order[city] == 0 for city in cities]
    s.add(Or(first_city))
    for city in cities:
        s.add(If(order[city] == 0, start[city] == 1, True))
    
    last_city = [order[city] == 3 for city in cities]
    s.add(Or(last_city))
    for city in cities:
        s.add(If(order[city] == 3, end[city] == 13, True))
    
    # Consecutive cities must have matching days and direct flights
    for i in cities:
        for j in cities:
            if i != j:
                # If j immediately follows i in order
                cond = And(order[i] + 1 == order[j])
                # Then end[i] must equal start[j]
                s.add(If(cond, end[i] == start[j], True))
                # And there must be a direct flight between i and j
                flight_ok = Or((i, j) in direct_flights, (j, i) in direct_flights)
                s.add(If(cond, flight_ok, True))
    
    # Stuttgart must include day 7 and day 13 (already covered by end=13)
    s.add(start['Stuttgart'] <= 7)
    s.add(end['Stuttgart'] >= 7)
    
    # Madrid must include at least one day between 1 and 4
    s.add(start['Madrid'] <= 4)
    s.add(end['Madrid'] >= 1)
    
    # Check feasibility
    if s.check() == sat:
        model = s.model()
        # Extract start and end days for each city
        itinerary = []
        for city in cities:
            start_val = model.evaluate(start[city]).as_long()
            end_val = model.evaluate(end[city]).as_long()
            itinerary.append({
                'place': city,
                'start': start_val,
                'end': end_val
            })
        # Sort by start day
        itinerary.sort(key=lambda x: x['start'])
        # Format day ranges
        result = []
        for visit in itinerary:
            if visit['start'] == visit['end']:
                day_range = f"Day {visit['start']}"
            else:
                day_range = f"Day {visit['start']}-{visit['end']}"
            result.append({'day_range': day_range, 'place': visit['place']})
        
        # Output as JSON
        print(json.dumps({'itinerary': result}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()