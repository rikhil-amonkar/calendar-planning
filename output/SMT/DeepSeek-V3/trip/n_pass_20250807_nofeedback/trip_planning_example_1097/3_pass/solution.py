from z3 import *
import json

def solve_itinerary():
    # Cities and their codes
    cities = {
        'Reykjavik': 0,
        'Riga': 1,
        'Oslo': 2,
        'Lyon': 3,
        'Dubrovnik': 4,
        'Madrid': 5,
        'Warsaw': 6,
        'London': 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [5, 2, 7],  # Reykjavik to Madrid, Oslo, London
        1: [6, 2],      # Riga to Warsaw, Oslo
        2: [5, 4, 0, 6, 3, 7, 1],  # Oslo to Madrid, Dubrovnik, Reykjavik, Warsaw, Lyon, London, Riga
        3: [7, 5],      # Lyon to London, Madrid
        4: [2, 5],      # Dubrovnik to Oslo, Madrid
        5: [2, 7, 3, 6, 0, 4],  # Madrid to Oslo, London, Lyon, Warsaw, Reykjavik, Dubrovnik
        6: [0, 1, 2, 7, 5],  # Warsaw to Reykjavik, Riga, Oslo, London, Madrid
        7: [3, 5, 6, 2, 0]   # London to Lyon, Madrid, Warsaw, Oslo, Reykjavik
    }
    
    # Required days per city
    required_days = {
        0: 4,  # Reykjavik
        1: 2,  # Riga
        2: 3,  # Oslo
        3: 5,  # Lyon
        4: 2,  # Dubrovnik
        5: 2,  # Madrid
        6: 4,  # Warsaw
        7: 3   # London
    }
    
    # Create Z3 variables for each day (1..18)
    days = 18
    day_vars = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    s = Solver()
    
    # Each day variable must be one of the city codes
    for d in day_vars:
        s.add(Or([d == c for c in cities.values()]))
    
    # Constraint: total days per city must match required_days
    for city, req in required_days.items():
        s.add(Sum([If(d == city, 1, 0) for d in day_vars]) == req
    
    # Flight constraints: consecutive days must be either same city or connected by direct flight
    for i in range(days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        # For each city c, if current is c, then next_day must be in direct_flights[c] or c.
        constraints = []
        for c in cities.values():
            allowed_next = direct_flights[c] + [c]
            constraints.append(Implies(current == c, Or([next_day == allowed for allowed in allowed_next])))
        s.add(Or(constraints))
    
    # Riga constraint: must include day 4 or 5
    s.add(Or(day_vars[3] == 1, day_vars[4] == 1))  # days are 1-based, so day 4 is index 3, day 5 is index 4
    
    # Dubrovnik wedding: must include day 7 or 8
    s.add(Or(day_vars[6] == 4, day_vars[7] == 4))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_code = m.evaluate(day_vars[i]).as_long()
            city_name = city_names[city_code]
            itinerary.append({"day": day_num, "place": city_name})
        
        # Verify the solution meets all constraints
        # Check required days per city
        city_days = {c: 0 for c in cities.values()}
        for entry in itinerary:
            city_code = cities[entry['place']]
            city_days[city_code] += 1
        for city, req in required_days.items():
            assert city_days[city] == req, f"City {city_names[city]} has {city_days[city]} days, expected {req}"
        
        # Check Riga and Dubrovnik event constraints
        riga_days = [entry['day'] for entry in itinerary if entry['place'] == 'Riga']
        assert any(day in [4,5] for day in riga_days), "Riga constraint not met"
        
        dubrovnik_days = [entry['day'] for entry in itinerary if entry['place'] == 'Dubrovnik']
        assert any(day in [7,8] for day in dubrovnik_days), "Dubrovnik wedding constraint not met"
        
        # Check flight connections
        for i in range(len(itinerary) - 1):
            current_city = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if current_city != next_city:
                current_code = cities[current_city]
                next_code = cities[next_city]
                assert next_code in direct_flights[current_code], f"No direct flight from {current_city} to {next_city}"
        
        # Format the output as JSON
        output = {"itinerary": itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))