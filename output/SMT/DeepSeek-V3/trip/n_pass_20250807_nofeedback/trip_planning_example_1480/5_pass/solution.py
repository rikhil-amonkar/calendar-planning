import json
from z3 import *

def solve_itinerary():
    # Cities and required days
    cities = {
        'Geneva': 4,
        'Venice': 5,
        'Vienna': 4,
        'Vilnius': 4,
        'Madrid': 4,
        'Munich': 5,
        'Reykjavik': 2,
        'Riga': 2,
        'Brussels': 2,
        'Istanbul': 4
    }
    
    # Corrected direct flights (bidirectional)
    direct_flights = [
        ('Munich', 'Vienna'),
        ('Istanbul', 'Brussels'),
        ('Vienna', 'Vilnius'),
        ('Madrid', 'Munich'),
        ('Venice', 'Brussels'),
        ('Riga', 'Brussels'),
        ('Geneva', 'Istanbul'),
        ('Munich', 'Reykjavik'),
        ('Vienna', 'Istanbul'),
        ('Riga', 'Istanbul'),
        ('Reykjavik', 'Vienna'),
        ('Venice', 'Munich'),
        ('Madrid', 'Venice'),
        ('Vilnius', 'Istanbul'),
        ('Venice', 'Vienna'),
        ('Venice', 'Istanbul'),
        ('Reykjavik', 'Madrid'),
        ('Riga', 'Munich'),
        ('Munich', 'Istanbul'),
        ('Reykjavik', 'Brussels'),
        ('Vilnius', 'Brussels'),
        ('Vilnius', 'Munich'),
        ('Madrid', 'Vienna'),
        ('Vienna', 'Riga'),
        ('Geneva', 'Vienna'),
        ('Madrid', 'Brussels'),
        ('Vienna', 'Brussels'),
        ('Geneva', 'Brussels'),
        ('Geneva', 'Madrid'),
        ('Munich', 'Brussels'),
        ('Madrid', 'Istanbul'),
        ('Geneva', 'Munich'),
        ('Riga', 'Vilnius')
    ]
    
    # Standardize city names and make flights bidirectional
    flight_set = set()
    for c1, c2 in direct_flights:
        c1 = c1.replace('Venice', 'Venice').replace('Munich', 'Munich')
        c2 = c2.replace('Venice', 'Venice').replace('Munich', 'Munich')
        flight_set.add((c1, c2))
        flight_set.add((c2, c1))
    
    # Create solver
    s = Solver()
    
    days = 27
    city_list = sorted(cities.keys())
    city_to_int = {city: i for i, city in enumerate(city_list)}
    int_to_city = {i: city for i, city in enumerate(city_list)}
    
    # Decision variables: city for each day
    day_city = [Int(f'day_{day}') for day in range(days)]
    
    # Each day must be assigned to a valid city
    for dc in day_city:
        s.add(Or([dc == city_to_int[city] for city in city_list]))
    
    # Flight constraints between consecutive days
    for i in range(days - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        s.add(Or(
            current == next_day,
            *[And(current == city_to_int[c1], next_day == city_to_int[c2]) 
              for c1, c2 in flight_set]
        ))
    
    # Fixed constraints
    # Geneva days 1-4 (0-3 in zero-based)
    for day in range(4):
        s.add(day_city[day] == city_to_int['Geneva'])
    
    # Venice workshop days 7-11 (6-10)
    for day in range(6, 11):
        s.add(day_city[day] == city_to_int['Venice'])
    
    # Vilnius friends days 20-23 (19-22)
    for day in range(19, 23):
        s.add(day_city[day] == city_to_int['Vilnius'])
    
    # Brussels wedding days 26-27 (25-26)
    s.add(day_city[25] == city_to_int['Brussels'])
    s.add(day_city[26] == city_to_int['Brussels'])
    
    # Duration constraints
    for city, req_days in cities.items():
        city_idx = city_to_int[city]
        # Count days where city is either current or next in flight
        total = Sum([If(day_city[i] == city_idx, 1, 0) for i in range(days)])
        s.add(total >= req_days)
    
    # Solve
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Build itinerary accounting for flight days
        for day in range(days):
            current_city = int_to_city[model.evaluate(day_city[day]).as_long()]
            
            # Check if this is a flight day
            if day > 0:
                prev_city = int_to_city[model.evaluate(day_city[day - 1]).as_long()]
                if prev_city != current_city:
                    itinerary.append({
                        "day": day + 1,
                        "place": f"{prev_city} -> {current_city}"
                    })
                    continue
            
            itinerary.append({
                "day": day + 1,
                "place": current_city
            })
        
        # Verify all constraints are met
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            places = entry["place"].split(" -> ") if " -> " in entry["place"] else [entry["place"]]
            for city in places:
                city_counts[city] += 1
        
        for city, req in cities.items():
            assert city_counts[city] >= req, f"City {city} has only {city_counts[city]} days (needs {req})"
        
        return json.dumps({"itinerary": itinerary}, indent=2)
    else:
        return json.dumps({"error": "No valid itinerary found"}, indent=2)

print(solve_itinerary())