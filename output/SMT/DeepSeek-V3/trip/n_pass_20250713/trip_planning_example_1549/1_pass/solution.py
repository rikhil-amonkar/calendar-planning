import json
from z3 import *

def solve_itinerary():
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
    
    connected = {}
    for city in cities:
        connected[city] = []
    for a, b in direct_flights:
        connected[a].append(b)
        connected[b].append(a)
    
    total_days = 28
    day_vars = [Int(f"day_{i}") for i in range(1, total_days + 1)]
    
    city_ids = {city: idx for idx, city in enumerate(cities.keys(), 1)}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    for day in day_vars:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    for i in range(total_days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        s.add(Or(
            current == next_day,
            Or([And(current == city_ids[a], next_day == city_ids[b]) for a, b in direct_flights] +
               [And(current == city_ids[b], next_day == city_ids[a]) for a, b in direct_flights])
        ))
    
    for city in cities:
        total = Sum([If(day == city_ids[city], 1, 0) for day in day_vars])
        s.add(total == cities[city])
    
    # Riga from day 5 to day 8 (4 days)
    for i in range(5, 9):
        s.add(day_vars[i - 1] == city_ids["Riga"])
    
    # Tallinn between day 18 and 20 (3 days)
    s.add(Or(
        And(day_vars[17] == city_ids["Tallinn"], day_vars[18] == city_ids["Tallinn"], day_vars[19] == city_ids["Tallinn"]),  # 18-20
        And(day_vars[17] == city_ids["Tallinn"], day_vars[18] == city_ids["Tallinn"], day_vars[19] != city_ids["Tallinn"]),  # 18-19
        And(day_vars[17] != city_ids["Tallinn"], day_vars[18] == city_ids["Tallinn"], day_vars[19] == city_ids["Tallinn"])   # 19-20
    ))
    
    # Milan between day 24 and 26 (3 days)
    s.add(Or(
        And(day_vars[23] == city_ids["Milan"], day_vars[24] == city_ids["Milan"], day_vars[25] == city_ids["Milan"]),  # 24-26
        And(day_vars[23] == city_ids["Milan"], day_vars[24] == city_ids["Milan"], day_vars[25] != city_ids["Milan"]),  # 24-25
        And(day_vars[23] != city_ids["Milan"], day_vars[24] == city_ids["Milan"], day_vars[25] == city_ids["Milan"])   # 25-26
    ))
    
    if s.check() == sat:
        m = s.model()
        assignments = [m.evaluate(day).as_long() for day in day_vars]
        
        itinerary = []
        current_city = id_to_city[assignments[0]]
        start_day = 1
        
        for i in range(1, total_days):
            if assignments[i] != assignments[i-1]:
                # Add the stay up to previous day
                if start_day == i:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_city})
                # Add flight day (i is transition)
                itinerary.append({"day_range": f"Day {i}", "place": current_city})
                new_city = id_to_city[assignments[i]]
                itinerary.append({"day_range": f"Day {i}", "place": new_city})
                current_city = new_city
                start_day = i + 1
        
        # Add the last stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        # Verify the itinerary meets all constraints
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