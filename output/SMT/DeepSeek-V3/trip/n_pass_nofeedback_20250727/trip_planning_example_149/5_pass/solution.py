from z3 import *
import json

def solve_itinerary():
    s = Solver()

    # Days 1-10
    days = range(1, 11)
    cities = {'London': 0, 'Santorini': 1, 'Istanbul': 2}
    city_vars = [Int(f'day_{day}') for day in days]

    # Each day must be one of the cities
    for day in days:
        s.add(Or([city_vars[day-1] == val for val in cities.values()]))

    # Total days constraints
    s.add(Sum([If(city_vars[i] == cities['London'], 1, 0) for i in range(10)]) == 3)
    s.add(Sum([If(city_vars[i] == cities['Santorini'], 1, 0) for i in range(10)]) == 6)
    s.add(Sum([If(city_vars[i] == cities['Istanbul'], 1, 0) for i in range(10)]) == 3)

    # Conference days in Santorini
    s.add(city_vars[4] == cities['Santorini'])  # Day 5
    s.add(city_vars[9] == cities['Santorini'])  # Day 10

    # Flight constraints - only direct connections
    for i in range(9):
        current = city_vars[i]
        next_day = city_vars[i+1]
        s.add(Implies(current != next_day,
                      Or(
                          And(current == cities['London'], next_day == cities['Santorini']),
                          And(current == cities['Santorini'], next_day == cities['London']),
                          And(current == cities['London'], next_day == cities['Istanbul']),
                          And(current == cities['Istanbul'], next_day == cities['London'])
                      )))

    # Additional constraints to help the solver
    # Must start or end in Santorini (since days 5 and 10 are there)
    s.add(Or(city_vars[0] == cities['Santorini'], city_vars[-1] == cities['Santorini']))

    # Must have at least one transition through London
    s.add(Or([And(city_vars[i] == cities['London'], city_vars[i+1] != cities['London']) for i in range(9)]))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        city_names = {v: k for k, v in cities.items()}
        for day in days:
            city_index = model.evaluate(city_vars[day-1]).as_long()
            itinerary.append({'day': day, 'place': city_names[city_index]})

        # Verify counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1

        if (counts['London'] == 3 and counts['Santorini'] == 6 and 
            counts['Istanbul'] == 3 and itinerary[4]['place'] == 'Santorini' and 
            itinerary[9]['place'] == 'Santorini'):
            return json.dumps({'itinerary': itinerary}, indent=2)
        else:
            return json.dumps({'error': 'Invalid solution found'}, indent=2)
    else:
        return json.dumps({'error': 'No valid itinerary found'}, indent=2)

print(solve_itinerary())