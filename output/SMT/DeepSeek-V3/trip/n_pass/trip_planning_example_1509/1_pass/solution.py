import json
from z3 import *

def solve_itinerary():
    # Cities involved
    cities = ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 
              'Helsinki', 'Oslo', 'Santorini', 'Lyon']
    
    # Direct flights as a set of tuples (from, to)
    direct_flights = {
        ('Warsaw', 'Riga'), ('Warsaw', 'Tallinn'), ('Copenhagen', 'Helsinki'),
        ('Lyon', 'Paris'), ('Copenhagen', 'Warsaw'), ('Lyon', 'Oslo'),
        ('Paris', 'Oslo'), ('Paris', 'Riga'), ('Krakow', 'Helsinki'),
        ('Paris', 'Tallinn'), ('Copenhagen', 'Krakow'), ('Oslo', 'Riga'),
        ('Krakow', 'Warsaw'), ('Paris', 'Helsinki'), ('Copenhagen', 'Santorini'),
        ('Helsinki', 'Warsaw'), ('Helsinki', 'Riga'), ('Copenhagen', 'Riga'),
        ('Paris', 'Krakow'), ('Copenhagen', 'Oslo'), ('Oslo', 'Tallinn'),
        ('Oslo', 'Helsinki'), ('Copenhagen', 'Tallinn'), ('Riga', 'Tallinn'),
        ('Helsinki', 'Tallinn'), ('Paris', 'Copenhagen'), ('Paris', 'Warsaw'),
        ('Santorini', 'Oslo'), ('Oslo', 'Warsaw')
    }
    
    # Make flights bidirectional
    all_flights = set()
    for (a, b) in direct_flights:
        all_flights.add((a, b))
        all_flights.add((b, a))
    
    # Create Z3 variables for each day's location
    days = 25
    day_vars = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    # City to integer mapping
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    s = Solver()
    
    # Each day variable must be a valid city index
    for day_var in day_vars:
        s.add(day_var >= 0, day_var < len(cities))
    
    # Duration constraints
    # Paris: 5 days total
    s.add(Sum([If(day_var == city_to_int['Paris'], 1, 0) for day_var in day_vars]) == 5)
    # Warsaw: 2 days
    s.add(Sum([If(day_var == city_to_int['Warsaw'], 1, 0) for day_var in day_vars]) == 2)
    # Krakow: 2 days
    s.add(Sum([If(day_var == city_to_int['Krakow'], 1, 0) for day_var in day_vars]) == 2)
    # Tallinn: 2 days
    s.add(Sum([If(day_var == city_to_int['Tallinn'], 1, 0) for day_var in day_vars]) == 2)
    # Riga: 2 days
    s.add(Sum([If(day_var == city_to_int['Riga'], 1, 0) for day_var in day_vars]) == 2)
    # Copenhagen: 5 days
    s.add(Sum([If(day_var == city_to_int['Copenhagen'], 1, 0) for day_var in day_vars]) == 5)
    # Helsinki: 5 days
    s.add(Sum([If(day_var == city_to_int['Helsinki'], 1, 0) for day_var in day_vars]) == 5)
    # Oslo: 5 days
    s.add(Sum([If(day_var == city_to_int['Oslo'], 1, 0) for day_var in day_vars]) == 5)
    # Santorini: 2 days
    s.add(Sum([If(day_var == city_to_int['Santorini'], 1, 0) for day_var in day_vars]) == 2)
    # Lyon: 4 days
    s.add(Sum([If(day_var == city_to_int['Lyon'], 1, 0) for day_var in day_vars]) == 4)
    
    # Specific day constraints
    # Paris friends between day 4 and 8 (inclusive)
    s.add(Or([day_vars[i] == city_to_int['Paris'] for i in range(3, 8)]))  # days 4-8 (1-based is 3-7 in 0-based)
    
    # Workshop in Krakow between day 17 and 18
    s.add(Or(day_vars[16] == city_to_int['Krakow'], day_vars[17] == city_to_int['Krakow']))
    
    # Wedding in Riga between day 23 and 24
    s.add(Or(day_vars[22] == city_to_int['Riga'], day_vars[23] == city_to_int['Riga']))
    
    # Friend in Helsinki between day 18 and 22
    s.add(Or([day_vars[i] == city_to_int['Helsinki'] for i in range(17, 22)]))  # days 18-22 (0-based 17-21)
    
    # Relatives in Santorini between day 12 and 13
    s.add(Or(day_vars[11] == city_to_int['Santorini'], day_vars[12] == city_to_int['Santorini']))
    
    # Flight constraints: consecutive days in different cities must have a direct flight
    for i in range(days - 1):
        current_day = day_vars[i]
        next_day = day_vars[i + 1]
        # Either stay in the same city or take a direct flight
        s.add(Or(
            current_day == next_day,
            *[And(current_day == city_to_int[a], next_day == city_to_int[b]) 
              for (a, b) in all_flights if a in city_to_int and b in city_to_int]
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            city_idx = model.evaluate(day_vars[i]).as_long()
            itinerary.append({"day": i + 1, "place": int_to_city[city_idx]})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))