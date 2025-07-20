from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Munich', 'Porto'),
        ('Split', 'Milan'),
        ('Milan', 'Porto'),
        ('Munich', 'Krakow'),
        ('Munich', 'Milan'),
        ('Dubrovnik', 'Munich'),
        ('Krakow', 'Split'),
        ('Krakow', 'Milan'),
        ('Munich', 'Split')
    ]
    # Ensure flights are bidirectional
    direct_flights_set = set(direct_flights)
    for a, b in direct_flights:
        direct_flights_set.add((b, a))
    
    # Days are 1..16
    days = 16
    # Create a solver instance
    s = Solver()
    
    # Variables: for each day, which city is visited
    day_city = [Int(f'day_{d}_city') for d in range(1, days + 1)]
    for d in range(1, days + 1):
        s.add(day_city[d - 1] >= 0, day_city[d - 1] < len(cities))
    
    # Constraints for flights between cities
    for d in range(1, days):
        city_today = day_city[d - 1]
        city_tomorrow = day_city[d]
        # Either stay in the same city or take a direct flight
        same_city = city_today == city_tomorrow
        possible_flights = []
        for a, b in direct_flights_set:
            a_idx = city_map[a]
            b_idx = city_map[b]
            possible_flights.append(And(city_today == a_idx, city_tomorrow == b_idx))
        s.add(Or(same_city, Or(possible_flights)))
    
    # Duration constraints
    for city in cities:
        total_days = Sum([If(day_city[d - 1] == city_map[city], 1, 0) for d in range(1, days + 1)])
        if city == 'Dubrovnik':
            s.add(total_days == 4)
        elif city == 'Split':
            s.add(total_days == 3)
        elif city == 'Milan':
            s.add(total_days == 3)
        elif city == 'Porto':
            s.add(total_days == 4)
        elif city == 'Krakow':
            s.add(total_days == 2)
        elif city == 'Munich':
            s.add(total_days == 5)
    
    # Event constraints
    # Wedding in Milan between day 11 and 13
    s.add(Or([day_city[d - 1] == city_map['Milan'] for d in range(11, 14)]))
    # Friends in Krakow between day 8 and 9
    s.add(Or([day_city[d - 1] == city_map['Krakow'] for d in range(8, 10)]))
    # Annual show in Munich from day 4 to 8
    s.add(Or([day_city[d - 1] == city_map['Munich'] for d in range(4, 9)]))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        for d in range(1, days + 1):
            city_idx = m.evaluate(day_city[d - 1]).as_long()
            city = cities[city_idx]
            if city != current_city:
                if current_city is not None:
                    itinerary.append({'day_range': f'Day {start_day}-{d - 1}', 'place': current_city})
                current_city = city
                start_day = d
        itinerary.append({'day_range': f'Day {start_day}-{days}', 'place': current_city})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute the solver and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))