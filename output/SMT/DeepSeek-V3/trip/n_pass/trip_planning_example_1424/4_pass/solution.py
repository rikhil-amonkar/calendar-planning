import json
from z3 import *

def solve_scheduling_problem():
    # Cities and their required days
    cities = {
        'Warsaw': 3,
        'Porto': 5,
        'Naples': 4,
        'Brussels': 3,
        'Split': 3,
        'Reykjavik': 5,
        'Amsterdam': 4,
        'Lyon': 3,
        'Helsinki': 4,
        'Valencia': 2
    }
    
    # Direct flights (corrected for typos)
    direct_flights = [
        ('Amsterdam', 'Warsaw'),
        ('Helsinki', 'Brussels'),
        ('Helsinki', 'Warsaw'),
        ('Reykjavik', 'Brussels'),
        ('Amsterdam', 'Lyon'),
        ('Amsterdam', 'Naples'),
        ('Amsterdam', 'Reykjavik'),
        ('Naples', 'Valencia'),
        ('Porto', 'Brussels'),
        ('Amsterdam', 'Split'),
        ('Lyon', 'Split'),
        ('Warsaw', 'Split'),
        ('Porto', 'Amsterdam'),
        ('Helsinki', 'Split'),
        ('Brussels', 'Lyon'),
        ('Porto', 'Lyon'),
        ('Reykjavik', 'Warsaw'),
        ('Brussels', 'Valencia'),
        ('Valencia', 'Lyon'),
        ('Porto', 'Warsaw'),
        ('Warsaw', 'Valencia'),
        ('Amsterdam', 'Helsinki'),
        ('Porto', 'Valencia'),
        ('Warsaw', 'Brussels'),
        ('Warsaw', 'Naples'),
        ('Naples', 'Split'),
        ('Helsinki', 'Naples'),
        ('Helsinki', 'Reykjavik'),
        ('Amsterdam', 'Valencia'),
        ('Naples', 'Brussels')
    ]
    
    # Unique list of cities
    city_list = list(cities.keys())
    num_days = 27
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..27)
    day = [Int(f'day_{i+1}') for i in range(num_days)]
    
    # Create a mapping from city name to integer
    city_to_int = {city: idx for idx, city in enumerate(city_list)}
    int_to_city = {idx: city for idx, city in enumerate(city_list)}
    
    s = Solver()
    
    # Each day must be assigned a valid city index
    for d in day:
        s.add(And(d >= 0, d < len(city_list)))
    
    # Fixed events:
    # Porto between day 1 and 5 (inclusive)
    for i in range(0, 5):  # days 1-5 (0-based: 0..4)
        s.add(day[i] == city_to_int['Porto'])
    
    # Amsterdam between day 5 and 8 (5,6,7,8)
    # day5 is Porto, day6 is Amsterdam
    s.add(day[4] == city_to_int['Porto'])  # day5 is Porto
    s.add(day[5] == city_to_int['Amsterdam'])  # day6 is Amsterdam
    s.add(day[6] == city_to_int['Amsterdam'])  # day7 is Amsterdam
    s.add(day[7] == city_to_int['Amsterdam'])  # day8 is Amsterdam
    
    # Helsinki wedding between day 8 and 11 (8,9,10,11)
    s.add(day[7] == city_to_int['Helsinki'])  # day8 is Helsinki
    s.add(day[8] == city_to_int['Helsinki'])  # day9 is Helsinki
    s.add(day[9] == city_to_int['Helsinki'])  # day10 is Helsinki
    s.add(day[10] == city_to_int['Helsinki'])  # day11 is Helsinki
    
    # Naples conference during day 17-20 (17,18,19,20)
    s.add(day[16] == city_to_int['Naples'])  # day17 is Naples
    s.add(day[17] == city_to_int['Naples'])  # day18 is Naples
    s.add(day[18] == city_to_int['Naples'])  # day19 is Naples
    s.add(day[19] == city_to_int['Naples'])  # day20 is Naples
    
    # Brussels show from day 20 to 22 (20,21,22)
    s.add(day[19] == city_to_int['Brussels'])  # day20 is Brussels
    s.add(day[20] == city_to_int['Brussels'])  # day21 is Brussels
    s.add(day[21] == city_to_int['Brussels'])  # day22 is Brussels
    
    # Constraints for city days:
    # For each city, the total occurrences in day array must equal the required days.
    for city, required_days in cities.items():
        city_idx = city_to_int[city]
        s.add(Sum([If(day[i] == city_idx, 1, 0) for i in range(num_days)]) == required_days)
    
    # Flight constraints: consecutive days can only be the same city or connected by a direct flight
    for i in range(num_days - 1):
        current_city = day[i]
        next_city = day[i+1]
        # Either same city, or (current_city, next_city) is in direct_flights
        same_city = (current_city == next_city)
        flight_possible = Or([And(current_city == city_to_int[c1], next_city == city_to_int[c2]) for (c1, c2) in direct_flights] +
                           [And(current_city == city_to_int[c2], next_city == city_to_int[c1]) for (c1, c2) in direct_flights])
        s.add(Or(same_city, flight_possible))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(num_days):
            city_idx = model.evaluate(day[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({"day": i+1, "place": city})
        
        result = {"itinerary": itinerary}
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No valid itinerary found"}, indent=2)

# Execute the solver
print(solve_scheduling_problem())