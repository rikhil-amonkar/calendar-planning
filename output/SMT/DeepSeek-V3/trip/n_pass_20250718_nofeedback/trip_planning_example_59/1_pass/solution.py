from z3 import *

def solve_trip_scheduling():
    # Cities: 1 = Bucharest, 2 = Lyon, 3 = Porto
    cities = {'Bucharest': 1, 'Lyon': 2, 'Porto': 3}
    num_days = 16
    days_in_lyon = 7
    days_in_bucharest = 7
    days_in_porto = 4
    
    # Create Z3 variables for each day's city
    day_city = [Int(f'day_{i}_city') for i in range(1, num_days + 1)]
    
    s = Solver()
    
    # Constraint: each day's city must be 1, 2, or 3
    for day in day_city:
        s.add(Or(day == cities['Bucharest'], day == cities['Lyon'], day == cities['Porto']))
    
    # Constraint: transitions must be valid (only Bucharest <-> Lyon or Lyon <-> Porto)
    for i in range(num_days - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        s.add(Or(
            current == next_day,  # same city
            And(current == cities['Bucharest'], next_day == cities['Lyon']),  # B -> L
            And(current == cities['Lyon'], next_day == cities['Bucharest']),  # L -> B
            And(current == cities['Lyon'], next_day == cities['Porto']),     # L -> P
            And(current == cities['Porto'], next_day == cities['Lyon'])      # P -> L
        ))
    
    # Constraint: total days in each city
    total_b = Sum([If(day == cities['Bucharest'], 1, 0) for day in day_city])
    total_l = Sum([If(day == cities['Lyon'], 1, 0) for day in day_city])
    total_p = Sum([If(day == cities['Porto'], 1, 0) for day in day_city])
    
    s.add(total_b == days_in_bucharest)
    s.add(total_l == days_in_lyon)
    s.add(total_p == days_in_porto)
    
    # Constraint: Bucharest must be visited within the first 7 days (wedding)
    s.add(Or([day_city[i] == cities['Bucharest'] for i in range(7)]))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        city_names = {1: 'Bucharest', 2: 'Lyon', 3: 'Porto'}
        for i in range(num_days):
            day_num = i + 1
            city_val = m[day_city[i]].as_long()
            city = city_names[city_val]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify the solution meets all constraints
        # (Z3 should ensure this, but it's good to double-check)
        b_days = sum(1 for entry in itinerary if entry['place'] == 'Bucharest')
        l_days = sum(1 for entry in itinerary if entry['place'] == 'Lyon')
        p_days = sum(1 for entry in itinerary if entry['place'] == 'Porto')
        assert b_days == 7
        assert l_days == 7
        assert p_days == 4
        
        # Check transitions are valid
        for i in range(num_days - 1):
            current = itinerary[i]['place']
            next_p = itinerary[i + 1]['place']
            if current != next_p:
                valid = (current == 'Bucharest' and next_p == 'Lyon') or \
                        (current == 'Lyon' and next_p == 'Bucharest') or \
                        (current == 'Lyon' and next_p == 'Porto') or \
                        (current == 'Porto' and next_p == 'Lyon')
                assert valid, f"Invalid transition from {current} to {next_p} on day {i+1}"
        
        # Check wedding constraint: Bucharest in first 7 days
        wedding_ok = any(entry['place'] == 'Bucharest' for entry in itinerary[:7])
        assert wedding_ok, "Wedding constraint not met"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_trip_scheduling()
import json
print(json.dumps(result, indent=2))