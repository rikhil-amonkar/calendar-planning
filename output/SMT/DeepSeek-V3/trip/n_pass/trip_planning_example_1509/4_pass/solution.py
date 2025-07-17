from z3 import *
import json

def solve_itinerary():
    # Cities involved
    cities = ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 
              'Helsinki', 'Oslo', 'Santorini', 'Lyon']
    city_vars = {city: [Bool(f'{city}_{day}') for day in range(1, 26)] for city in cities}
    
    # Direct flights: bidirectional unless specified otherwise (but the problem says direct flights, so assuming bidirectional)
    direct_flights = {
        'Warsaw': ['Riga', 'Tallinn', 'Copenhagen', 'Helsinki', 'Paris', 'Krakow', 'Oslo'],
        'Riga': ['Warsaw', 'Tallinn', 'Helsinki', 'Paris', 'Oslo', 'Copenhagen', 'Krakow'],
        'Tallinn': ['Warsaw', 'Riga', 'Oslo', 'Helsinki', 'Copenhagen', 'Paris'],
        'Copenhagen': ['Helsinki', 'Warsaw', 'Lyon', 'Oslo', 'Santorini', 'Krakow', 'Riga', 'Tallinn', 'Paris'],
        'Helsinki': ['Copenhagen', 'Warsaw', 'Tallinn', 'Oslo', 'Riga', 'Krakow', 'Paris'],
        'Oslo': ['Lyon', 'Paris', 'Riga', 'Tallinn', 'Helsinki', 'Copenhagen', 'Warsaw', 'Krakow', 'Santorini'],
        'Santorini': ['Copenhagen', 'Oslo'],
        'Lyon': ['Paris', 'Oslo', 'Copenhagen'],
        'Paris': ['Lyon', 'Oslo', 'Riga', 'Tallinn', 'Warsaw', 'Copenhagen', 'Helsinki', 'Krakow'],
        'Krakow': ['Warsaw', 'Helsinki', 'Copenhagen', 'Paris', 'Oslo', 'Riga']
    }
    
    s = Solver()
    
    # Exactly one city per day
    for day in range(1, 26):
        s.add(Or([city_vars[city][day-1] for city in cities]))
        for city1 in cities:
            for city2 in cities:
                if city1 != city2:
                    s.add(Implies(city_vars[city1][day-1], Not(city_vars[city2][day-1])))
    
    # Flight constraints: consecutive days must be in the same city or connected by a direct flight
    for day in range(1, 25):
        current_day_vars = [city_vars[city][day-1] for city in cities]
        next_day_vars = [city_vars[city][day] for city in cities]
        transitions = []
        for city1 in cities:
            for city2 in cities:
                if city1 == city2:
                    # Stay in the same city
                    transitions.append(And(city_vars[city1][day-1], city_vars[city2][day]))
                else:
                    if city2 in direct_flights.get(city1, []):
                        transitions.append(And(city_vars[city1][day-1], city_vars[city2][day]))
        s.add(Or(transitions))
    
    # Duration constraints
    # Paris: 5 days
    s.add(Sum([If(city_vars['Paris'][day], 1, 0) for day in range(25)]) == 5)
    # Warsaw: 2 days
    s.add(Sum([If(city_vars['Warsaw'][day], 1, 0) for day in range(25)]) == 2)
    # Krakow: 2 days
    s.add(Sum([If(city_vars['Krakow'][day], 1, 0) for day in range(25)]) == 2)
    # Tallinn: 2 days
    s.add(Sum([If(city_vars['Tallinn'][day], 1, 0) for day in range(25)]) == 2)
    # Riga: 2 days
    s.add(Sum([If(city_vars['Riga'][day], 1, 0) for day in range(25)]) == 2)
    # Copenhagen: 5 days
    s.add(Sum([If(city_vars['Copenhagen'][day], 1, 0) for day in range(25)]) == 5)
    # Helsinki: 5 days
    s.add(Sum([If(city_vars['Helsinki'][day], 1, 0) for day in range(25)]) == 5)
    # Oslo: 5 days
    s.add(Sum([If(city_vars['Oslo'][day], 1, 0) for day in range(25)]) == 5)
    # Santorini: 2 days
    s.add(Sum([If(city_vars['Santorini'][day], 1, 0) for day in range(25)]) == 2)
    # Lyon: 4 days
    s.add(Sum([If(city_vars['Lyon'][day], 1, 0) for day in range(25)]) == 4)
    
    # Event constraints
    # Paris between day 4 and day 8 (inclusive) to meet friends: at least one day in this interval must be in Paris
    s.add(Or([city_vars['Paris'][day] for day in range(3, 8)]))  # days 4-8 (0-based: 3-7)
    # Workshop in Krakow between day 17 and 18: must be in Krakow on day 16 or 17 (0-based: 16,17)
    s.add(Or(city_vars['Krakow'][16], city_vars['Krakow'][17]))
    # Wedding in Riga between day 23 and 24: must be in Riga on day 22 or 23 (0-based: 22,23)
    s.add(Or(city_vars['Riga'][22], city_vars['Riga'][23]))
    # Friend in Helsinki between day 18 and 22: at least one day in this interval must be in Helsinki
    s.add(Or([city_vars['Helsinki'][day] for day in range(17, 22)]))  # days 18-22 (0-based:17-21)
    # Relatives in Santorini between day 12 and 13: must be in Santorini on day 11 or 12 (0-based:11,12)
    s.add(Or(city_vars['Santorini'][11], city_vars['Santorini'][12]))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, 26):
            for city in cities:
                if m.evaluate(city_vars[city][day-1]):
                    itinerary.append({'day': day, 'place': city})
                    break
        # Verify all constraints are met
        # (Additional checks could be added here)
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
print(json.dumps(result, indent=2))