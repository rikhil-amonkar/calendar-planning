from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Madrid', 'Seville', 'Porto', 'Stuttgart']
    city_map = {c: idx for idx, c in enumerate(cities)}
    Madrid, Seville, Porto, Stuttgart = 0, 1, 2, 3
    
    # Direct flights: adjacency list
    direct_flights = {
        Madrid: [Seville, Porto],
        Seville: [Madrid, Porto],
        Porto: [Madrid, Seville, Stuttgart],
        Stuttgart: [Porto]
    }
    
    # Create solver
    s = Solver()
    
    # Variables: day 1 to 13, each is a city (0-3)
    days = [Int(f'day_{i}') for i in range(1, 14)]
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in [Madrid, Seville, Porto, Stuttgart]]))
    
    # Constraint: transitions between days must be via direct flights or same city
    for i in range(len(days) - 1):
        current_day = days[i]
        next_day = days[i + 1]
        s.add(Or(
            current_day == next_day,
            And(next_day in direct_flights[current_day]),
            And(current_day in direct_flights[next_day])
        ))
    
    # Total days per city
    total_madrid = Sum([If(d == Madrid, 1, 0) for d in days])
    total_seville = Sum([If(d == Seville, 1, 0) for d in days])
    total_porto = Sum([If(d == Porto, 1, 0) for d in days])
    total_stuttgart = Sum([If(d == Stuttgart, 1, 0) for d in days])
    
    s.add(total_madrid == 4)
    s.add(total_seville == 2)
    s.add(total_porto == 3)
    s.add(total_stuttgart == 7)
    
    # Stuttgart must be on day 7 and 13
    s.add(days[6] == Stuttgart)  # day 7 is index 6
    s.add(days[12] == Stuttgart)  # day 13 is index 12
    
    # Madrid must be visited between day 1 and 4 (at least one day in 1-4)
    s.add(Or([days[i] == Madrid for i in range(4)]))  # days 1-4 are indices 0-3
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        city_names = ['Madrid', 'Seville', 'Porto', 'Stuttgart']
        for i in range(1, 14):
            city_val = m.evaluate(days[i-1]).as_long()
            itinerary.append({'day': i, 'place': city_names[city_val]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No solution found'}

# Generate the itinerary
itinerary = solve_itinerary()
print(itinerary)