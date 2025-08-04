from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Mykonos', 'Krakow', 'Vilnius', 'Helsinki', 'Dubrovnik', 'Oslo', 'Madrid', 'Paris']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights as tuples of city indices
    direct_flights = [
        (city_to_idx['Oslo'], city_to_idx['Krakow']),
        (city_to_idx['Oslo'], city_to_idx['Paris']),
        (city_to_idx['Paris'], city_to_idx['Madrid']),
        (city_to_idx['Helsinki'], city_to_idx['Vilnius']),
        (city_to_idx['Oslo'], city_to_idx['Madrid']),
        (city_to_idx['Oslo'], city_to_idx['Helsinki']),
        (city_to_idx['Helsinki'], city_to_idx['Krakow']),
        (city_to_idx['Dubrovnik'], city_to_idx['Helsinki']),
        (city_to_idx['Dubrovnik'], city_to_idx['Madrid']),
        (city_to_idx['Oslo'], city_to_idx['Dubrovnik']),
        (city_to_idx['Krakow'], city_to_idx['Paris']),
        (city_to_idx['Madrid'], city_to_idx['Mykonos']),
        (city_to_idx['Oslo'], city_to_idx['Vilnius']),
        (city_to_idx['Krakow'], city_to_idx['Vilnius']),
        (city_to_idx['Helsinki'], city_to_idx['Paris']),
        (city_to_idx['Vilnius'], city_to_idx['Paris']),
        (city_to_idx['Helsinki'], city_to_idx['Madrid']),
    ]
    # Make flights bidirectional
    bidirectional_flights = set()
    for a, b in direct_flights:
        bidirectional_flights.add((a, b))
        bidirectional_flights.add((b, a))
    direct_flights = bidirectional_flights
    
    # Create solver
    s = Solver()
    
    # Variables: day_1 to day_18, each can be one of the cities (0-7)
    days = [Int(f'day_{i}') for i in range(1, 19)]
    for day in days:
        s.add(day >= 0, day < 8)
    
    # Constraints for fixed days
    # Oslo between day 1 and day 2 (i.e., day 1 is Oslo, day 2 could be Oslo or another city)
    s.add(days[0] == city_to_idx['Oslo'])  # day 1 is Oslo
    # Dubrovnik from day 2 to day 4 (days 2, 3, 4)
    s.add(days[1] == city_to_idx['Dubrovnik'])  # day 2
    s.add(days[2] == city_to_idx['Dubrovnik'])  # day 3
    s.add(days[3] == city_to_idx['Dubrovnik'])  # day 4
    # Mykonos between day 15 and 18 (must be there for 4 days, so days 15-18)
    s.add(days[14] == city_to_idx['Mykonos'])  # day 15
    s.add(days[15] == city_to_idx['Mykonos'])  # day 16
    s.add(days[16] == city_to_idx['Mykonos'])  # day 17
    s.add(days[17] == city_to_idx['Mykonos'])  # day 18
    
    # Flight transitions: consecutive days must be same city or connected by direct flight
    for i in range(17):  # days 1..18, so pairs (1,2), ..., (17,18)
        current = days[i]
        next_day = days[i+1]
        # Either stay in the same city or move via direct flight
        s.add(Or(current == next_day, 
                 *[And(current == a, next_day == b) for a, b in direct_flights]))
    
    # Duration constraints for each city
    def count_days(city_idx):
        return Sum([If(days[i] == city_idx, 1, 0) for i in range(18)])
    
    s.add(count_days(city_to_idx['Mykonos']) == 4)
    s.add(count_days(city_to_idx['Krakow']) == 5)
    s.add(count_days(city_to_idx['Vilnius']) == 2)
    s.add(count_days(city_to_idx['Helsinki']) == 2)
    s.add(count_days(city_to_idx['Dubrovnik']) == 3)  # days 2-4 (3 days)
    s.add(count_days(city_to_idx['Oslo']) == 2)  # day 1 and possibly day 2
    s.add(count_days(city_to_idx['Madrid']) == 5)
    s.add(count_days(city_to_idx['Paris']) == 2)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(18):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = cities[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Generate and print the itinerary
import json
result = solve_itinerary()
print(json.dumps(result, indent=2))