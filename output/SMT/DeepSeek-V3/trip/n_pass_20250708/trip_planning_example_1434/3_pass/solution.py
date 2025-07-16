from z3 import *
import json

def solve_itinerary():
    cities = {
        "Rome": 3,
        "Mykonos": 2,
        "Lisbon": 2,
        "Frankfurt": 5,
        "Nice": 3,
        "Stuttgart": 4,
        "Venice": 4,
        "Dublin": 2,
        "Bucharest": 2,
        "Seville": 5
    }
    
    direct_flights = {
        "Rome": ["Stuttgart", "Venice", "Mykonos", "Seville", "Frankfurt", "Bucharest", "Dublin", "Lisbon", "Nice"],
        "Stuttgart": ["Rome", "Venice", "Frankfurt", "Lisbon"],
        "Venice": ["Rome", "Stuttgart", "Frankfurt", "Lisbon", "Nice", "Dublin"],
        "Dublin": ["Bucharest", "Lisbon", "Nice", "Frankfurt", "Rome", "Venice", "Seville"],
        "Mykonos": ["Rome", "Nice"],
        "Lisbon": ["Seville", "Bucharest", "Venice", "Dublin", "Rome", "Frankfurt", "Nice", "Stuttgart"],
        "Frankfurt": ["Venice", "Rome", "Dublin", "Nice", "Stuttgart", "Bucharest", "Lisbon"],
        "Nice": ["Mykonos", "Dublin", "Venice", "Rome", "Frankfurt", "Lisbon"],
        "Bucharest": ["Dublin", "Lisbon", "Rome", "Frankfurt"],
        "Seville": ["Lisbon", "Rome", "Dublin"]
    }
    
    total_days = 23
    
    s = Solver()
    
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    day_to_city = [Int(f"day_{i}") for i in range(1, total_days + 1)]
    
    for day in range(total_days):
        s.add(Or([day_to_city[day] == city_ids[city] for city in cities]))
    
    for city, days in cities.items():
        s.add(Sum([If(day_to_city[day] == city_ids[city], 1, 0) for day in range(total_days)]) == days)
    
    # Frankfurt between day 1-5 (0-based 0-4)
    s.add(Or([day_to_city[day] == city_ids["Frankfurt"] for day in range(5)]))
    
    # Mykonos includes day 10 or 11 (0-based 9 or 10)
    s.add(Or(day_to_city[9] == city_ids["Mykonos"], day_to_city[10] == city_ids["Mykonos"]))
    
    # Seville between day 13-17 (0-based 12-16)
    s.add(Or([day_to_city[day] == city_ids["Seville"] for day in range(12, 17)]))
    
    for day in range(total_days - 1):
        current = day_to_city[day]
        next_ = day_to_city[day + 1]
        s.add(Or(
            current == next_,
            *[And(current == city_ids[src], next_ == city_ids[dst]) 
              for src in direct_flights for dst in direct_flights[src]
        ))
    
    if s.check() == sat:
        model = s.model()
        assignments = []
        for day in range(total_days):
            city_id = model.eval(day_to_city[day]).as_long()
            city = id_to_city[city_id]
            assignments.append((day + 1, city))
        
        itinerary = []
        i = 0
        n = len(assignments)
        while i < n:
            day, city = assignments[i]
            start_day = day
            # Check if next day is different (flight)
            if i < n - 1 and assignments[i + 1][1] != city:
                # Flight day: current day is city and next city
                next_city = assignments[i + 1][1]
                itinerary.append({"day_range": f"Day {day}", "place": city})
                itinerary.append({"day_range": f"Day {day}", "place": next_city})
                i += 1
            else:
                # Find consecutive same city
                j = i
                while j < n and assignments[j][1] == city:
                    j += 1
                end_day = assignments[j - 1][0]
                if start_day == end_day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
                i = j
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))