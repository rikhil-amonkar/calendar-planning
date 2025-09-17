import json
from z3 import *

def main():
    # Initialize solver
    solver = Solver()
    
    # Cities encoding
    Milan, Seville, Naples = 0, 1, 2
    cities = {Milan: "Milan", Seville: "Seville", Naples: "Naples"}
    
    # Direct flights (symmetric)
    direct_flights = [(Milan, Seville), (Seville, Milan), (Naples, Milan), (Milan, Naples)]
    
    # Day variables (1-indexed)
    n_days = 12
    start = [Int(f'start_{i}') for i in range(1, n_days+1)]
    end = [Int(f'end_{i}') for i in range(1, n_days+1)]
    fly = [Bool(f'fly_{i}') for i in range(1, n_days+1)]
    
    # Initial constraint: start city on day 1 must be valid
    solver.add(Or([start[0] == city for city in cities]))
    
    # Constraints for each day
    for i in range(n_days):
        # Valid cities
        solver.add(Or([start[i] == city for city in cities]))
        solver.add(Or([end[i] == city for city in cities]))
        
        # Flight constraints
        solver.add(If(fly[i], 
                      Or([And(start[i] == a, end[i] == b) for a, b in direct_flights]),
                      start[i] == end[i]))
        
        # Chain days: next start equals current end
        if i < n_days - 1:
            solver.add(start[i+1] == end[i])
    
    # Total days per city (including travel days)
    days_in_city = [0, 0, 0]
    for c in cities:
        days_in_city[c] = Sum([If(Or(start[i] == c, And(fly[i], end[i] == c)), 1, 0) 
                              for i in range(n_days)])
    
    # Problem constraints
    solver.add(days_in_city[Naples] == 3)
    solver.add(days_in_city[Seville] == 4)
    solver.add(days_in_city[Milan] == 7)
    
    # Seville must be visited from day 9 to 12 (inclusive)
    for i in range(8, 12):  # days 9-12 (0-indexed 8-11)
        solver.add(Or(start[i] == Seville, And(fly[i], end[i] == Seville)))
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        
        # Extract flight days
        flight_days = []
        for i in range(n_days):
            if is_true(model.eval(fly[i])):
                flight_days.append(i+1)  # Convert to 1-indexed
        
        # Determine segments
        segments = []
        current_city = model.eval(start[0])
        start_day = 1
        
        for day in range(1, n_days+1):
            i = day - 1
            if day in flight_days or day == n_days:
                end_day = day
                segments.append({
                    'start': start_day,
                    'end': end_day,
                    'city': current_city
                })
                start_day = day
                current_city = model.eval(end[i])
        
        # Format output
        itinerary = []
        for seg in segments:
            if seg['start'] == seg['end']:
                day_range = f"Day {seg['start']}"
            else:
                day_range = f"Day {seg['start']}-{seg['end']}"
            itinerary.append({
                'day_range': day_range,
                'place': cities[seg['city'].as_long()]
            })
        
        print(json.dumps({'itinerary': itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()