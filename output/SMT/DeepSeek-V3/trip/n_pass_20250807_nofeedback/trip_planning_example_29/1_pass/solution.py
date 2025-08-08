from z3 import *

def solve_itinerary():
    # Days are 1..10
    days = 10
    # For each day, which city are we in?
    day_city = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    s = Solver()
    
    # Assign each day_city to a city code (we'll use 0, 1, 2)
    city_codes = {'Krakow': 0, 'Dubrovnik': 1, 'Frankfurt': 2}
    code_to_city = {0: 'Krakow', 1: 'Dubrovnik', 2: 'Frankfurt'}
    
    for day in day_city:
        s.add(Or(day == city_codes['Krakow'], day == city_codes['Dubrovnik'], day == city_codes['Frankfurt']))
    
    # Constraint: Wedding in Krakow on days 9 and 10
    s.add(day_city[8] == city_codes['Krakow'])  # day 9 is index 8 (1-based vs 0-based)
    s.add(day_city[9] == city_codes['Krakow'])  # day 10
    
    # Count days in each city
    def count_days(city_code):
        return Sum([If(day == city_code, 1, 0) for day in day_city])
    
    s.add(count_days(city_codes['Krakow']) == 2)
    s.add(count_days(city_codes['Dubrovnik']) == 7)
    s.add(count_days(city_codes['Frankfurt']) == 3)
    
    # Flight constraints: transitions only between connected cities
    # Connected pairs: Frankfurt-Krakow, Dubrovnik-Frankfurt
    for i in range(days - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        # Possible transitions:
        # current and next_day can be the same (no flight)
        # Or between connected cities
        s.add(Or(
            current == next_day,  # stay in the same city
            And(current == city_codes['Frankfurt'], next_day == city_codes['Krakow']),
            And(current == city_codes['Krakow'], next_day == city_codes['Frankfurt']),
            And(current == city_codes['Dubrovnik'], next_day == city_codes['Frankfurt']),
            And(current == city_codes['Frankfurt'], next_day == city_codes['Dubrovnik'])
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_code = m.evaluate(day_city[i]).as_long()
            city = code_to_city[city_code]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify the counts
        krakow_days = sum(1 for entry in itinerary if entry['place'] == 'Krakow')
        dubrovnik_days = sum(1 for entry in itinerary if entry['place'] == 'Dubrovnik')
        frankfurt_days = sum(1 for entry in itinerary if entry['place'] == 'Frankfurt')
        assert krakow_days == 2
        assert dubrovnik_days == 7
        assert frankfurt_days == 3
        
        # Verify transitions
        for i in range(days - 1):
            current = itinerary[i]['place']
            next_place = itinerary[i + 1]['place']
            if current != next_place:
                assert (current == 'Frankfurt' and next_place == 'Krakow') or \
                       (current == 'Krakow' and next_place == 'Frankfurt') or \
                       (current == 'Dubrovnik' and next_place == 'Frankfurt') or \
                       (current == 'Frankfurt' and next_place == 'Dubrovnik'), \
                       f"Invalid flight from {current} to {next_place}"
        
        # Verify wedding days
        assert itinerary[8]['place'] == 'Krakow'  # day 9
        assert itinerary[9]['place'] == 'Krakow'  # day 10
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found")