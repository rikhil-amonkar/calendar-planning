from z3 import *
import json

def solve_itinerary():
    cities = {
        "Santorini": 5,
        "Krakow": 5,
        "Paris": 5,
        "Vilnius": 3,
        "Munich": 5,
        "Geneva": 2,
        "Amsterdam": 4,
        "Budapest": 5,
        "Split": 4
    }
    
    city_list = list(cities.keys())
    city_to_id = {city: idx for idx, city in enumerate(city_list)}
    
    # Flight connections (bidirectional)
    flight_pairs = [
        ("Paris", "Krakow"), ("Paris", "Amsterdam"), ("Paris", "Split"), ("Paris", "Geneva"), ("Paris", "Budapest"), ("Paris", "Vilnius"),
        ("Krakow", "Split"), ("Krakow", "Munich"), ("Krakow", "Amsterdam"), ("Krakow", "Vilnius"),
        ("Vilnius", "Munich"), ("Vilnius", "Split"), ("Vilnius", "Amsterdam"), ("Vilnius", "Krakow"),
        ("Munich", "Split"), ("Munich", "Amsterdam"), ("Munich", "Geneva"), ("Munich", "Krakow"), ("Munich", "Budapest"), ("Munich", "Paris"),
        ("Geneva", "Amsterdam"), ("Geneva", "Split"), ("Geneva", "Munich"), ("Geneva", "Budapest"), ("Geneva", "Santorini"),
        ("Amsterdam", "Split"), ("Amsterdam", "Budapest"), ("Amsterdam", "Santorini"), ("Amsterdam", "Krakow"),
        ("Budapest", "Munich"), ("Budapest", "Geneva"),
        ("Split", "Geneva"), ("Split", "Vilnius"), ("Split", "Munich"), ("Split", "Amsterdam"), ("Split", "Krakow"),
        ("Santorini", "Amsterdam")
    ]
    
    # Create a set of all possible direct flight connections (bidirectional)
    flight_connections = set()
    for a, b in flight_pairs:
        flight_connections.add((city_to_id[a], city_to_id[b]))
        flight_connections.add((city_to_id[b], city_to_id[a]))
    
    # Create Z3 variables: for each day (1..30), the city on that day (0-based index)
    day_city = [Int(f"day_{i}") for i in range(30)]
    
    s = Solver()
    
    # Each day's city must be one of the 9 cities
    for day in range(30):
        s.add(day_city[day] >= 0)
        s.add(day_city[day] < len(city_list))
    
    # City duration constraints
    for city, days in cities.items():
        city_id = city_to_id[city]
        s.add(Sum([If(day_city[day] == city_id, 1, 0) for day in range(30)]) == days)
    
    # Specific date ranges constraints (1-based to 0-based)
    # Santorini between day 25-29 (0-based: 24-28)
    s.add(Or([day_city[day] == city_to_id["Santorini"] for day in range(24, 29)]))
    
    # Krakow between day 18-22 (0-based: 17-21)
    s.add(Or([day_city[day] == city_to_id["Krakow"] for day in range(17, 22)]))
    
    # Paris between day 11-15 (0-based: 10-14)
    s.add(Or([day_city[day] == city_to_id["Paris"] for day in range(10, 15)]))
    
    # Flight constraints: consecutive days must be same city or connected by a direct flight
    for day in range(29):
        current = day_city[day]
        next_ = day_city[day + 1]
        s.add(Or(
            current == next_,
            And([Or(And(current == a, next_ == b)) for (a, b) in flight_connections])
        ))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        # Track the current city and start day of the stay
        current_city_id = m.evaluate(day_city[0]).as_long()
        current_city = city_list[current_city_id]
        start_day = 1  # 1-based
        
        for day in range(1, 30):
            next_city_id = m.evaluate(day_city[day]).as_long()
            if next_city_id == current_city_id:
                continue
            else:
                # Flight day: day is the transition day (1-based)
                # Add the stay up to day
                if start_day <= day:
                    itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_city})
                # Add the flight day entries (day is the flight day)
                itinerary.append({"day_range": f"Day {day+1}", "place": current_city})
                itinerary.append({"day_range": f"Day {day+1}", "place": city_list[next_city_id]})
                current_city_id = next_city_id
                current_city = city_list[current_city_id]
                start_day = day + 2  # next day is the start of the new city
        
        # Add the last stay
        if start_day <= 30:
            itinerary.append({"day_range": f"Day {start_day}-30", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))