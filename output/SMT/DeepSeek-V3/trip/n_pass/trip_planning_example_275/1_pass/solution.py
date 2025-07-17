from z3 import *

def solve_itinerary():
    # Cities
    Split, Vilnius, Santorini, Madrid = 0, 1, 2, 3
    cities = {0: 'Split', 1: 'Vilnius', 2: 'Santorini', 3: 'Madrid'}
    
    # Direct flights: adjacency list
    direct_flights = {
        Split: [Vilnius, Madrid],
        Vilnius: [Split],
        Madrid: [Split, Santorini],
        Santorini: [Madrid]
    }
    
    # Total days
    total_days = 14
    
    # Create Z3 variables: each day is assigned a city
    day_city = [Int(f'day_{i}_city') for i in range(1, total_days + 1)]
    
    s = Solver()
    
    # Each day's city must be one of the four cities
    for day in range(total_days):
        s.add(Or(
            day_city[day] == Split,
            day_city[day] == Vilnius,
            day_city[day] == Santorini,
            day_city[day] == Madrid
        ))
    
    # Constraint: days 13 and 14 (index 12 and 13) must be Santorini
    s.add(day_city[12] == Santorini)
    s.add(day_city[13] == Santorini)
    
    # Constraints for city visits:
    # Split: 5 days
    split_days = Sum([If(day_city[i] == Split, 1, 0) for i in range(total_days)])
    s.add(split_days == 5)
    
    # Vilnius: 4 days
    vilnius_days = Sum([If(day_city[i] == Vilnius, 1, 0) for i in range(total_days)])
    s.add(vilnius_days == 4)
    
    # Santorini: 2 days (already fixed days 13 and 14)
    # So no additional constraint needed
    
    # Madrid: 6 days
    madrid_days = Sum([If(day_city[i] == Madrid, 1, 0) for i in range(total_days)])
    s.add(madrid_days == 6)
    
    # Flight constraints: consecutive days in different cities must have a direct flight
    for i in range(total_days - 1):
        current_city = day_city[i]
        next_city = day_city[i + 1]
        # If cities are different, then there must be a direct flight
        s.add(Implies(
            current_city != next_city,
            Or([next_city == dst for dst in direct_flights[current_city]])
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(total_days):
            city_code = model.evaluate(day_city[day]).as_long()
            itinerary.append({
                'day': day + 1,
                'place': cities[city_code]
            })
        
        # Verify the counts
        counts = {city: 0 for city in cities.values()}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        # Prepare the output
        output = {
            'itinerary': itinerary
        }
        return output
    else:
        return None

# Execute the solver
result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No valid itinerary found.")