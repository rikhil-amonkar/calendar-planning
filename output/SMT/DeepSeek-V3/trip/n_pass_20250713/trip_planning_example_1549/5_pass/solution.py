import json
from z3 import *

def solve_itinerary():
    # Cities and required days
    cities = {
        "Prague": 5,
        "Tallinn": 3,
        "Warsaw": 2,
        "Porto": 3,
        "Naples": 5,
        "Milan": 3,
        "Lisbon": 5,
        "Santorini": 5,
        "Riga": 4,
        "Stockholm": 2
    }
    
    # Direct flight connections (undirected)
    direct_flights = [
        ("Riga", "Prague"),
        ("Stockholm", "Milan"),
        ("Riga", "Milan"),
        ("Lisbon", "Stockholm"),
        ("Stockholm", "Santorini"),
        ("Naples", "Warsaw"),
        ("Lisbon", "Warsaw"),
        ("Naples", "Milan"),
        ("Lisbon", "Naples"),
        ("Riga", "Tallinn"),
        ("Tallinn", "Prague"),
        ("Stockholm", "Warsaw"),
        ("Riga", "Warsaw"),
        ("Lisbon", "Riga"),
        ("Riga", "Stockholm"),
        ("Lisbon", "Porto"),
        ("Lisbon", "Prague"),
        ("Milan", "Porto"),
        ("Prague", "Milan"),
        ("Lisbon", "Milan"),
        ("Warsaw", "Porto"),
        ("Warsaw", "Tallinn"),
        ("Santorini", "Milan"),
        ("Stockholm", "Prague"),
        ("Stockholm", "Tallinn"),
        ("Warsaw", "Milan"),
        ("Santorini", "Naples"),
        ("Warsaw", "Prague")
    ]
    
    # Create flight connection graph
    connections = {city: set() for city in cities}
    for a, b in direct_flights:
        connections[a].add(b)
        connections[b].add(a)
    
    total_days = 28
    day_vars = [Int(f"day_{i}") for i in range(total_days)]
    
    # City to ID mapping
    city_ids = {city: idx for idx, city in enumerate(cities.keys(), 1)}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    # Pre-assign fixed stays
    # Riga: days 5-8 (indices 4-7)
    for i in range(4, 8):
        s.add(day_vars[i] == city_ids["Riga"])
    
    # Tallinn: days 18-20 (indices 17-19)
    s.add(Or(
        And(day_vars[17] == city_ids["Tallinn"], day_vars[18] == city_ids["Tallinn"], day_vars[19] == city_ids["Tallinn"]),
        And(day_vars[17] == city_ids["Tallinn"], day_vars[18] == city_ids["Tallinn"], day_vars[19] != city_ids["Tallinn"]),
        And(day_vars[17] != city_ids["Tallinn"], day_vars[18] == city_ids["Tallinn"], day_vars[19] == city_ids["Tallinn"])
    ))
    
    # Milan: days 24-26 (indices 23-25)
    s.add(Or(
        And(day_vars[23] == city_ids["Milan"], day_vars[24] == city_ids["Milan"], day_vars[25] == city_ids["Milan"]),
        And(day_vars[23] == city_ids["Milan"], day_vars[24] == city_ids["Milan"], day_vars[25] != city_ids["Milan"]),
        And(day_vars[23] != city_ids["Milan"], day_vars[24] == city_ids["Milan"], day_vars[25] == city_ids["Milan"])
    ))
    
    # Each day must be assigned to a valid city
    for day in day_vars:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Flight transitions must be between connected cities
    for i in range(total_days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        s.add(Or(
            current == next_day,  # Stay in same city
            Or([And(current == city_ids[a], next_day == city_ids[b]) for a, b in direct_flights] +
               [And(current == city_ids[b], next_day == city_ids[a]) for a, b in direct_flights])
        ))
    
    # Total days per city must match requirements
    for city in cities:
        total = Sum([If(day == city_ids[city], 1, 0) for day in day_vars])
        s.add(total == cities[city])
    
    # Solve and generate itinerary
    if s.check() == sat:
        m = s.model()
        assignments = [m.evaluate(day).as_long() for day in day_vars]
        
        itinerary = []
        current_city = id_to_city[assignments[0]]
        start_day = 1
        
        for i in range(1, total_days):
            if assignments[i] != assignments[i - 1]:
                if start_day == i:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_city})
                itinerary.append({"day_range": f"Day {i}", "place": current_city})
                new_city = id_to_city[assignments[i]]
                itinerary.append({"day_range": f"Day {i}", "place": new_city})
                current_city = new_city
                start_day = i + 1
        
        # Add last stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        # Verify all constraints are satisfied
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            day_range = entry["day_range"]
            place = entry["place"]
            if '-' in day_range:
                start, end = map(int, day_range.replace("Day ", "").split('-'))
                duration = end - start + 1
            else:
                duration = 1
            city_days[place] += duration
        
        for city in cities:
            assert city_days[city] == cities[city], f"City {city} has {city_days[city]} days, expected {cities[city]}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))