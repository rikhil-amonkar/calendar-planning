from z3 import *

def solve_itinerary():
    s = Solver()

    days = range(1, 13)
    cities = ['Naples', 'Seville', 'Milan']
    city_map = {c: i for i, c in enumerate(cities)}
    
    # Variables for each day's city
    city_vars = [Int(f'day_{day}') for day in days]
    
    # Each day must be assigned to a valid city
    for day in days:
        s.add(Or([city_vars[day-1] == i for i in range(3)]))
    
    # Flight constraints (only direct connections)
    for prev_day, next_day in zip(days[:-1], days[1:]):
        prev_city = city_vars[prev_day-1]
        next_city = city_vars[next_day-1]
        s.add(Or(
            prev_city == next_city,  # Stay in same city
            And(prev_city == city_map['Milan'], next_city == city_map['Seville']),
            And(prev_city == city_map['Seville'], next_city == city_map['Milan']),
            And(prev_city == city_map['Naples'], next_city == city_map['Milan']),
            And(prev_city == city_map['Milan'], next_city == city_map['Naples'])
        ))
    
    # Count days in each city
    naples_days = Sum([If(city_vars[day-1] == city_map['Naples'], 1, 0) for day in days])
    seville_days = Sum([If(city_vars[day-1] == city_map['Seville'], 1, 0) for day in days])
    milan_days = Sum([If(city_vars[day-1] == city_map['Milan'], 1, 0) for day in days])
    
    s.add(naples_days == 3)
    s.add(seville_days == 4)
    s.add(milan_days == 7)
    
    # Must be in Seville from day 9 to 12
    for day in range(9, 13):
        s.add(city_vars[day-1] == city_map['Seville'])
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        assigned_cities = [m.evaluate(city_vars[day-1]).as_long() for day in days]
        
        itinerary = []
        current_city = assigned_cities[0]
        start_day = 1
        
        for day in range(1, 13):
            if assigned_cities[day-1] != current_city:
                # Add previous stay
                if start_day != day - 1:
                    itinerary.append({
                        'day_range': f'Day {start_day}-{day-1}',
                        'place': cities[current_city]
                    })
                else:
                    itinerary.append({
                        'day_range': f'Day {start_day}',
                        'place': cities[current_city]
                    })
                # Add flight day (both cities)
                itinerary.append({
                    'day_range': f'Day {day}',
                    'place': cities[current_city]
                })
                itinerary.append({
                    'day_range': f'Day {day}',
                    'place': cities[assigned_cities[day-1]]
                })
                current_city = assigned_cities[day-1]
                start_day = day
            elif day == 12:
                if start_day != day:
                    itinerary.append({
                        'day_range': f'Day {start_day}-{day}',
                        'place': cities[current_city]
                    })
                else:
                    itinerary.append({
                        'day_range': f'Day {day}',
                        'place': cities[current_city]
                    })
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))