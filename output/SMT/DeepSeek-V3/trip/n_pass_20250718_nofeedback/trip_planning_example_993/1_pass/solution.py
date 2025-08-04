from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Riga', 'Frankfurt', 'Amsterdam', 'Vilnius', 'London', 'Stockholm', 'Bucharest']
    city_vars = {city: [Bool(f"{city}_{day}") for day in range(1, 16)] for city in cities}
    
    # Direct flights
    direct_flights = {
        'London': ['Amsterdam', 'Bucharest', 'Frankfurt', 'Stockholm'],
        'Amsterdam': ['London', 'Stockholm', 'Frankfurt', 'Riga', 'Vilnius', 'Bucharest'],
        'Vilnius': ['Frankfurt', 'Riga', 'Amsterdam'],
        'Riga': ['Vilnius', 'Stockholm', 'Frankfurt', 'Bucharest', 'Amsterdam'],
        'Frankfurt': ['Vilnius', 'Amsterdam', 'Stockholm', 'Riga', 'Bucharest', 'London'],
        'Stockholm': ['Riga', 'Amsterdam', 'Frankfurt', 'London'],
        'Bucharest': ['London', 'Riga', 'Frankfurt', 'Amsterdam']
    }
    
    s = Solver()
    
    # Each day must be in exactly one city
    for day in range(1, 16):
        day_vars = [city_vars[city][day-1] for city in cities]
        s.add(Or(*day_vars))
        for c1 in cities:
            for c2 in cities:
                if c1 != c2:
                    s.add(Not(And(city_vars[c1][day-1], city_vars[c2][day-1])))
    
    # Duration constraints
    s.add(Sum([If(city_vars['Riga'][d], 1, 0) for d in range(15)]) == 2)
    s.add(Sum([If(city_vars['Frankfurt'][d], 1, 0) for d in range(15)]) == 3)
    s.add(Sum([If(city_vars['Amsterdam'][d], 1, 0) for d in range(15)]) == 2)
    s.add(Sum([If(city_vars['Vilnius'][d], 1, 0) for d in range(15)]) == 5)
    s.add(Sum([If(city_vars['London'][d], 1, 0) for d in range(15)]) == 2)
    s.add(Sum([If(city_vars['Stockholm'][d], 1, 0) for d in range(15)]) == 3)
    s.add(Sum([If(city_vars['Bucharest'][d], 1, 0) for d in range(15)]) == 4)
    
    # Event constraints
    # Amsterdam between day 2 and 3 (i.e., day 2 or 3)
    s.add(Or(city_vars['Amsterdam'][1], city_vars['Amsterdam'][2]))
    
    # Workshop in Vilnius between day 7 and 11 (inclusive)
    # At least one day in Vilnius during days 7-11 (1-based)
    s.add(Or([city_vars['Vilnius'][d] for d in range(6, 11)]))
    
    # Wedding in Stockholm between day 13 and 15 (inclusive)
    s.add(Or([city_vars['Stockholm'][d] for d in range(12, 15)]))
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for day in range(1, 15):
        current_day = day - 1
        next_day = day
        for c1 in cities:
            for c2 in cities:
                if c1 != c2:
                    # If day is c1 and day+1 is c2, then there must be a flight
                    s.add(Implies(
                        And(city_vars[c1][current_day], city_vars[c2][next_day]),
                        Or([c2 == x for x in direct_flights[c1]])
                    ))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 16):
            for city in cities:
                if is_true(model[city_vars[city][day-1]]):
                    itinerary.append({"day": day, "place": city})
                    break
        
        # Verify all constraints are met
        # (Additional checks can be added here)
        
        # Format the output
        output = {"itinerary": itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))