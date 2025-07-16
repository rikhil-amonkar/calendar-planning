from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Paris', 'Oslo', 'Porto', 'Geneva', 'Reykjavik']
    city_vars = {city: [Bool(f'{city}_{day}') for day in range(1, 24)] for city in cities}
    
    s = Solver()
    
    # Each day must be in exactly one city
    for day in range(1, 24):
        in_cities = [city_vars[city][day-1] for city in cities]
        s.add(Or(in_cities))
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                s.add(Not(And(in_cities[i], in_cities[j])))
    
    # Direct flights
    direct_flights = {
        'Paris': ['Oslo', 'Geneva', 'Porto', 'Reykjavik'],
        'Oslo': ['Paris', 'Geneva', 'Reykjavik', 'Porto'],
        'Porto': ['Paris', 'Geneva', 'Oslo'],
        'Geneva': ['Paris', 'Oslo', 'Porto'],
        'Reykjavik': ['Paris', 'Oslo']
    }
    
    for day in range(1, 23):
        current_day_vars = {city: city_vars[city][day-1] for city in cities}
        next_day_vars = {city: city_vars[city][day] for city in cities}
        
        # If changing cities, ensure direct flight
        for city1 in cities:
            for city2 in cities:
                if city1 != city2:
                    s.add(Implies(
                        And(current_day_vars[city1], next_day_vars[city2]),
                        city2 in direct_flights[city1]
                    ))
    
    # Fixed constraints
    # Geneva from day 1 to 7
    for day in range(1, 8):
        s.add(city_vars['Geneva'][day-1])
    
    # Oslo from day 19 to 23
    for day in range(19, 24):
        s.add(city_vars['Oslo'][day-1])
    
    # Total days per city
    s.add(Sum([If(city_vars['Paris'][d], 1, 0) for d in range(23)]) == 6)
    s.add(Sum([If(city_vars['Oslo'][d], 1, 0) for d in range(23)]) == 5)
    s.add(Sum([If(city_vars['Porto'][d], 1, 0) for d in range(23)]) == 7)
    s.add(Sum([If(city_vars['Geneva'][d], 1, 0) for d in range(23)]) == 7)
    s.add(Sum([If(city_vars['Reykjavik'][d], 1, 0) for d in range(23)]) == 2)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        sequence = []
        for day in range(1, 24):
            for city in cities:
                if is_true(model.eval(city_vars[city][day-1])):
                    sequence.append((day, city))
                    break
        
        # Process the sequence to build itinerary with flight days
        i = 0
        n = len(sequence)
        while i < n:
            current_day, current_city = sequence[i]
            j = i + 1
            while j < n and sequence[j][1] == current_city:
                j += 1
            end_day = sequence[j-1][0] if j <= n else current_day
            
            if i == 0:
                # First entry
                if current_day == end_day:
                    itinerary.append({"day_range": f"Day {current_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": current_city})
            else:
                prev_day, prev_city = sequence[i-1]
                if prev_city != current_city:
                    # Flight day
                    itinerary.append({"day_range": f"Day {current_day}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {current_day}", "place": current_city})
                    if j > i + 1:
                        itinerary.append({"day_range": f"Day {current_day+1}-{end_day}", "place": current_city})
                else:
                    if current_day == end_day:
                        itinerary.append({"day_range": f"Day {current_day}", "place": current_city})
                    else:
                        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": current_city})
            i = j
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))