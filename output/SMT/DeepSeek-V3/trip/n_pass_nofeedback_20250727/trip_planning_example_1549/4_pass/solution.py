from z3 import *

def solve_itinerary():
    # Cities and their codes
    cities = {
        'Prague': 0,
        'Tallinn': 1,
        'Warsaw': 2,
        'Porto': 3,
        'Naples': 4,
        'Milan': 5,
        'Lisbon': 6,
        'Santorini': 7,
        'Riga': 8,
        'Stockholm': 9
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Required days per city
    required_days = {
        'Prague': 5,
        'Tallinn': 3,
        'Warsaw': 2,
        'Porto': 3,
        'Naples': 5,
        'Milan': 3,
        'Lisbon': 5,
        'Santorini': 5,
        'Riga': 4,
        'Stockholm': 2
    }
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [8, 1, 5, 9, 2],  # Prague
        1: [8, 0, 9, 2],       # Tallinn
        2: [4, 6, 3, 9, 8, 5, 0, 1],  # Warsaw
        3: [6, 5, 2],          # Porto
        4: [2, 5, 6, 7],       # Naples
        5: [9, 8, 6, 0, 3, 4, 2, 7],  # Milan
        6: [9, 2, 8, 0, 5, 4, 3],  # Lisbon
        7: [5, 4],              # Santorini
        8: [0, 5, 1, 9, 2, 6],  # Riga
        9: [5, 6, 8, 0, 1, 2]   # Stockholm
    }
    
    # Create Z3 variables for each day (1..28)
    days = [Int(f'day_{i}') for i in range(1, 29)]
    
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Add constraints for required days per city
    for city, days_needed in required_days.items():
        city_code = cities[city]
        s.add(Sum([If(day == city_code, 1, 0) for day in days]) == days_needed)
    
    # Fixed constraints:
    # Riga from day 5 to day 8 (days 5,6,7,8)
    for d in [5, 6, 7, 8]:
        s.add(days[d-1] == cities['Riga'])
    
    # Tallinn between day 18 and 20 (3 days in Tallinn)
    s.add(Or(
        And(days[17] == cities['Tallinn'], days[18] == cities['Tallinn'], days[19] == cities['Tallinn']),  # 18-20
        And(days[16] == cities['Tallinn'], days[17] == cities['Tallinn'], days[18] == cities['Tallinn']),  # 17-19
        And(days[19] == cities['Tallinn'], days[20] == cities['Tallinn'], days[21] == cities['Tallinn'])   # 20-22
    ))
    
    # Milan between day 24 and 26 (3 days in Milan)
    s.add(Or(
        And(days[23] == cities['Milan'], days[24] == cities['Milan'], days[25] == cities['Milan']),  # 24-26
        And(days[22] == cities['Milan'], days[23] == cities['Milan'], days[24] == cities['Milan']),  # 23-25
        And(days[25] == cities['Milan'], days[26] == cities['Milan'], days[27] == cities['Milan'])   # 26-28
    ))
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(len(days) - 1):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(
            current == next_day,
            *[And(current == c1, next_day == c2) for c1 in direct_flights for c2 in direct_flights[c1]]
        ))
    
    # Additional constraints to help the solver
    # Ensure first day is a city with many connections (Lisbon)
    s.add(days[0] == cities['Lisbon'])
    
    # Ensure last day is a city with many connections (Milan)
    s.add(days[27] == cities['Milan'])
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 29):
            day_var = days[i-1]
            city_code = model[day_var].as_long()
            itinerary.append({'day': i, 'place': city_names[city_code]})
        
        # Verify the solution meets all constraints
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        for city, req in required_days.items():
            assert city_days[city] == req, f"City {city} has {city_days[city]} days instead of {req}"
        
        for i in range(len(itinerary) - 1):
            current = itinerary[i]['place']
            next_p = itinerary[i+1]['place']
            if current != next_p:
                current_code = cities[current]
                next_code = cities[next_p]
                assert next_code in direct_flights[current_code], f"No flight from {current} to {next_p}"
        
        assert itinerary[4]['place'] == 'Riga'
        assert itinerary[5]['place'] == 'Riga'
        assert itinerary[6]['place'] == 'Riga'
        assert itinerary[7]['place'] == 'Riga'
        
        # Verify Tallinn constraint is met
        tallinn_days = [i for i, x in enumerate(itinerary) if x['place'] == 'Tallinn']
        assert any(17 <= d <= 19 for d in tallinn_days), "Tallinn not between days 18-20"
        
        # Verify Milan constraint is met
        milan_days = [i for i, x in enumerate(itinerary) if x['place'] == 'Milan']
        assert any(23 <= d <= 25 for d in milan_days), "Milan not between days 24-26"
        
        output = {'itinerary': itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

itinerary = solve_itinerary()
import json
print(json.dumps(itinerary, indent=2))