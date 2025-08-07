from z3 import *

def solve_itinerary():
    # Define cities with unique identifiers
    cities = {
        'Venice': 0,
        'Reykjavik': 1,
        'Munich': 2,
        'Santorini': 3,
        'Manchester': 4,
        'Porto': 5,
        'Bucharest': 6,
        'Tallinn': 7,
        'Valencia': 8,
        'Vienna': 9
    }
    num_days = 24

    # Direct flights adjacency list (bidirectional)
    direct_flights = {
        cities['Bucharest']: [cities['Manchester'], cities['Valencia'], cities['Vienna'], cities['Munich']],
        cities['Manchester']: [cities['Bucharest'], cities['Santorini'], cities['Vienna'], cities['Venice'], cities['Porto'], cities['Munich']],
        cities['Munich']: [cities['Venice'], cities['Porto'], cities['Manchester'], cities['Reykjavik'], cities['Vienna'], cities['Valencia'], cities['Bucharest'], cities['Tallinn']],
        cities['Santorini']: [cities['Manchester'], cities['Venice'], cities['Vienna'], cities['Bucharest']],
        cities['Vienna']: [cities['Reykjavik'], cities['Valencia'], cities['Manchester'], cities['Porto'], cities['Venice'], cities['Santorini'], cities['Bucharest'], cities['Munich']],
        cities['Venice']: [cities['Munich'], cities['Santorini'], cities['Manchester'], cities['Vienna']],
        cities['Reykjavik']: [cities['Vienna'], cities['Munich']],
        cities['Porto']: [cities['Munich'], cities['Vienna'], cities['Manchester'], cities['Valencia']],
        cities['Valencia']: [cities['Vienna'], cities['Bucharest'], cities['Porto'], cities['Munich']],
        cities['Tallinn']: [cities['Munich']]
    }

    # Create Z3 variables for each day
    day = [Int(f'day_{i}') for i in range(num_days)]
    s = Solver()

    # Each day must be one of the cities
    for d in day:
        s.add(Or([d == c for c in cities.values()]))

    # Fixed constraints
    # Munich days 4-6
    s.add(day[3] == cities['Munich'])
    s.add(day[4] == cities['Munich'])
    s.add(day[5] == cities['Munich'])

    # Santorini between days 8-10
    s.add(Or([day[7] == cities['Santorini'], 
             day[8] == cities['Santorini'], 
             day[9] == cities['Santorini']]))

    # Valencia days 14-15
    s.add(Or(day[13] == cities['Valencia'], 
             day[14] == cities['Valencia']))

    # Flight transitions
    for i in range(num_days - 1):
        current = day[i]
        next_day = day[i+1]
        s.add(Or(
            current == next_day,
            Or([And(current == c1, next_day == c2) 
               for c1 in direct_flights 
               for c2 in direct_flights[c1]])
        ))

    # Duration constraints
    durations = {
        'Venice': 3,
        'Reykjavik': 2,
        'Munich': 3,
        'Santorini': 3,
        'Manchester': 3,
        'Porto': 3,
        'Bucharest': 5,
        'Tallinn': 4,
        'Valencia': 2,
        'Vienna': 5
    }
    for city, duration in durations.items():
        s.add(Sum([If(day[i] == cities[city], 1, 0) 
                  for i in range(num_days)]) == duration)

    if s.check() == sat:
        model = s.model()
        itinerary = []
        city_names = {v: k for k, v in cities.items()}
        for i in range(num_days):
            city_code = model.evaluate(day[i]).as_long()
            itinerary.append({'day': i+1, 'place': city_names[city_code]})
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")