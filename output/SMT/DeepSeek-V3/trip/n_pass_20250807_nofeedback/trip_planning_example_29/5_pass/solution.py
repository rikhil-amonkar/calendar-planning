from z3 import *

def solve_itinerary():
    # City codes
    Krakow, Dubrovnik, Frankfurt = 0, 1, 2
    code_to_city = {0: 'Krakow', 1: 'Dubrovnik', 2: 'Frankfurt'}
    
    # Create solver
    s = Solver()
    
    # Variables for each day's location (days 1-10)
    day_vars = [Int(f'day_{i}') for i in range(1, 11)]
    
    # Each day must be assigned to a valid city
    for day in day_vars:
        s.add(Or(day == Krakow, day == Dubrovnik, day == Frankfurt))
    
    # Wedding in Krakow on days 9-10
    s.add(day_vars[8] == Krakow)  # day 9
    s.add(day_vars[9] == Krakow)  # day 10
    
    # Count days in each city
    def count_days(city):
        return Sum([If(day == city, 1, 0) for day in day_vars])
    
    s.add(count_days(Krakow) == 2)
    s.add(count_days(Dubrovnik) == 7)
    s.add(count_days(Frankfurt) == 3)
    
    # Flight constraints - only allow valid transitions
    for i in range(9):  # Check transitions between days 1-9 and 2-10
        current = day_vars[i]
        next_day = day_vars[i+1]
        
        # Can stay in same city
        same_city = (current == next_day)
        
        # Or take valid flights
        frankfurt_krakow = And(current == Frankfurt, next_day == Krakow)
        krakow_frankfurt = And(current == Krakow, next_day == Frankfurt)
        dubrovnik_frankfurt = And(current == Dubrovnik, next_day == Frankfurt)
        frankfurt_dubrovnik = And(current == Frankfurt, next_day == Dubrovnik)
        
        s.add(Or(same_city, frankfurt_krakow, krakow_frankfurt, 
                dubrovnik_frankfurt, frankfurt_dubrovnik))
    
    # Solve and validate
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        for i in range(10):
            day_num = i + 1
            city_code = m.evaluate(day_vars[i]).as_long()
            city = code_to_city[city_code]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify counts
        counts = {'Krakow': 0, 'Dubrovnik': 0, 'Frankfurt': 0}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        assert counts['Krakow'] == 2
        assert counts['Dubrovnik'] == 7
        assert counts['Frankfurt'] == 3
        
        # Verify transitions
        for i in range(9):
            current = itinerary[i]['place']
            next_place = itinerary[i+1]['place']
            if current != next_place:
                valid = ((current == 'Frankfurt' and next_place == 'Krakow') or
                        (current == 'Krakow' and next_place == 'Frankfurt') or
                        (current == 'Dubrovnik' and next_place == 'Frankfurt') or
                        (current == 'Frankfurt' and next_place == 'Dubrovnik'))
                assert valid, f"Invalid flight from {current} to {next_place}"
        
        # Verify wedding days
        assert itinerary[8]['place'] == 'Krakow'
        assert itinerary[9]['place'] == 'Krakow'
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found")