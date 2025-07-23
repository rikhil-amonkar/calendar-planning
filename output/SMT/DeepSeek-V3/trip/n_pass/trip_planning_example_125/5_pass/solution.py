from z3 import *

def solve_itinerary():
    s = Solver()
    
    # Total days
    total_days = 15
    
    # Cities encoding
    cities = {'Stuttgart': 0, 'Seville': 1, 'Manchester': 2}
    city_names = {v: k for k, v in cities.items()}
    
    # Decision variables: city for each day
    city_day = [Int(f'day_{d}_city') for d in range(total_days)]
    
    # Each day must be assigned to a valid city
    for d in range(total_days):
        s.add(Or([city_day[d] == c for c in cities.values()]))
    
    # Flight constraints - only allowed transitions
    for d in range(total_days - 1):
        current = city_day[d]
        next_day = city_day[d + 1]
        
        # Can stay in same city
        same_city = current == next_day
        
        # Or take allowed flights
        man_to_sev = And(current == cities['Manchester'], next_day == cities['Seville'])
        sev_to_man = And(current == cities['Seville'], next_day == cities['Manchester'])
        man_to_stu = And(current == cities['Manchester'], next_day == cities['Stuttgart'])
        stu_to_man = And(current == cities['Stuttgart'], next_day == cities['Manchester'])
        
        s.add(Or(same_city, man_to_sev, sev_to_man, man_to_stu, stu_to_man))
    
    # Total days in each city (including overlaps)
    stuttgart_days = Sum([If(city_day[d] == cities['Stuttgart'], 1, 0) for d in range(total_days)])
    seville_days = Sum([If(city_day[d] == cities['Seville'], 1, 0) for d in range(total_days)])
    manchester_days = Sum([If(city_day[d] == cities['Manchester'], 1, 0) for d in range(total_days)])
    
    s.add(stuttgart_days == 6)
    s.add(seville_days == 7)
    s.add(manchester_days == 4)
    
    # Must visit Stuttgart between day 1-6 (0-based days 0-5)
    s.add(Or([city_day[d] == cities['Stuttgart'] for d in range(6)]))
    
    # Additional constraint: cannot have single-day stays in Manchester
    # This helps prevent invalid short stays
    for d in range(1, total_days - 1):
        prev = city_day[d - 1]
        current = city_day[d]
        next_ = city_day[d + 1]
        s.add(Not(And(prev != cities['Manchester'], current == cities['Manchester'], next_ != cities['Manchester'])))
    
    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Build the itinerary
        for d in range(total_days):
            city_code = model.evaluate(city_day[d]).as_long()
            itinerary.append({
                'day': d + 1,
                'place': city_names[city_code]
            })
        
        # Verify all constraints
        counts = {'Stuttgart': 0, 'Seville': 0, 'Manchester': 0}
        for day in itinerary:
            counts[day['place']] += 1
        
        assert counts['Stuttgart'] == 6
        assert counts['Seville'] == 7
        assert counts['Manchester'] == 4
        
        # Check flight constraints
        for d in range(total_days - 1):
            current = itinerary[d]['place']
            next_place = itinerary[d + 1]['place']
            
            if current != next_place:
                valid = (
                    (current == 'Manchester' and next_place in ['Seville', 'Stuttgart']) or
                    (next_place == 'Manchester' and current in ['Seville', 'Stuttgart'])
                )
                assert valid, f"Invalid flight from {current} to {next_place} on day {d + 1}"
        
        # Check Stuttgart visit in first 6 days
        stuttgart_in_first_6 = any(day['place'] == 'Stuttgart' for day in itinerary[:6])
        assert stuttgart_in_first_6, "Stuttgart not visited in first 6 days"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))