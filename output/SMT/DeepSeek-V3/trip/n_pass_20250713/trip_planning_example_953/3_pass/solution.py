from z3 import *
import json

def solve_itinerary():
    # Cities and required days
    cities = {
        "Salzburg": 4,
        "Stockholm": 2,
        "Venice": 5,
        "Frankfurt": 4,
        "Florence": 4,
        "Barcelona": 2,
        "Stuttgart": 3
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ("Barcelona", "Frankfurt"),
        ("Florence", "Frankfurt"),
        ("Stockholm", "Barcelona"),
        ("Barcelona", "Florence"),
        ("Venice", "Barcelona"),
        ("Stuttgart", "Barcelona"),
        ("Frankfurt", "Salzburg"),
        ("Stockholm", "Frankfurt"),
        ("Stuttgart", "Stockholm"),
        ("Stuttgart", "Frankfurt"),
        ("Venice", "Stuttgart"),
        ("Venice", "Frankfurt")
    ]
    
    # Make flight connections bidirectional
    flight_connections = {}
    for city in cities:
        flight_connections[city] = []
    for a, b in direct_flights:
        flight_connections[a].append(b)
        flight_connections[b].append(a)
    
    total_days = 18
    Day = 18  # Days are 1-based to 18
    
    # Create Z3 variables: city per day
    # day_city[d] represents the city on day d (1..18)
    day_city = [Int(f"day_{d}_city") for d in range(1, Day + 1)]
    
    # City to integer mapping
    city_to_int = {city: idx for idx, city in enumerate(cities.keys())}
    int_to_city = {idx: city for idx, city in enumerate(cities.keys())}
    
    s = Solver()
    
    # Each day_city must be a valid city index
    for d in range(Day):
        s.add(day_city[d] >= 0, day_city[d] < len(cities))
    
    # Constraint: Venice must be visited from day 1 to day 5 (inclusive)
    for d in range(5):  # days 1-5 (0-based 0..4)
        s.add(day_city[d] == city_to_int["Venice"])
    
    # Constraints on the number of days per city
    for city, days in cities.items():
        city_idx = city_to_int[city]
        s.add(Sum([If(day_city[d] == city_idx, 1, 0) for d in range(Day)]) == days)
    
    # Flight constraints: consecutive days must be the same city or connected by a flight
    for d in range(Day - 1):
        current_city = day_city[d]
        next_city = day_city[d + 1]
        # Either same city or connected
        same_city = current_city == next_city
        connected = Or([And(current_city == city_to_int[a], next_city == city_to_int[b]) 
                        for a, b in direct_flights] + 
                       [And(current_city == city_to_int[b], next_city == city_to_int[a]) 
                        for a, b in direct_flights])
        s.add(Or(same_city, connected))
    
    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        # Determine the sequence of cities from the model
        sequence = []
        for d in range(Day):
            city_idx = m.evaluate(day_city[d]).as_long()
            city = int_to_city[city_idx]
            sequence.append(city)
        
        # Now, process the sequence to create the itinerary with day ranges and flight days
        current_place = sequence[0]
        start_day = 1
        itinerary_json = []
        
        for d in range(1, Day):
            if sequence[d] != sequence[d-1]:
                # Flight occurs between d and d+1 (0-based, days start at 1)
                # Add the stay before the flight
                if start_day <= d:  # 0-based d is day (d+1)
                    itinerary_json.append({
                        "day_range": f"Day {start_day}-{d}",
                        "place": sequence[d-1]
                    })
                # Add the flight day: departure and arrival
                itinerary_json.append({
                    "day_range": f"Day {d}",
                    "place": sequence[d-1]
                })
                itinerary_json.append({
                    "day_range": f"Day {d}",
                    "place": sequence[d]
                })
                start_day = d + 1
        # Add the last stay
        itinerary_json.append({
            "day_range": f"Day {start_day}-{Day}",
            "place": sequence[-1]
        })
        
        # Verify the total days per city
        city_days = {city: 0 for city in cities}
        for entry in itinerary_json:
            day_range = entry["day_range"]
            place = entry["place"]
            if '-' in day_range:
                start, end = map(int, day_range.replace("Day ", "").split('-'))
                days = end - start + 1
            else:
                days = 1
            city_days[place] += days
        
        for city in cities:
            assert city_days[city] == cities[city], f"City {city} has {city_days[city]} days, expected {cities[city]}"
        
        return {"itinerary": itinerary_json}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))