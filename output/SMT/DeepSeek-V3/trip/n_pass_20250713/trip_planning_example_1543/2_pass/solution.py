from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Prague": 3,
        "Warsaw": 4,
        "Dublin": 3,
        "Athens": 3,
        "Vilnius": 4,
        "Porto": 5,
        "London": 3,
        "Seville": 2,
        "Lisbon": 5,
        "Dubrovnik": 3
    }
    
    # Direct flights (undirected)
    direct_flights = {
        "Warsaw": ["Vilnius", "London", "Athens", "Lisbon", "Porto", "Prague", "Dublin"],
        "Vilnius": ["Warsaw", "Athens"],
        "Prague": ["Athens", "Lisbon", "London", "Warsaw", "Dublin"],
        "Athens": ["Prague", "Vilnius", "Dublin", "Warsaw", "Dubrovnik", "Lisbon", "London"],
        "London": ["Prague", "Lisbon", "Dublin", "Warsaw", "Athens"],
        "Lisbon": ["London", "Porto", "Prague", "Athens", "Warsaw", "Dublin", "Seville"],
        "Porto": ["Lisbon", "Warsaw", "Seville", "Dublin"],
        "Dublin": ["London", "Athens", "Seville", "Dubrovnik", "Porto", "Lisbon", "Prague", "Warsaw"],
        "Seville": ["Dublin", "Porto", "Lisbon"],
        "Dubrovnik": ["Athens", "Dublin"]
    }
    
    # Fixed events
    fixed_events = [
        ("Prague", 1, 3),
        ("London", 3, 5),
        ("Lisbon", 5, 9),
        ("Porto", 16, 20),
        ("Warsaw", 20, 23)
    ]
    
    total_days = 26
    num_days = total_days
    
    # Create Z3 variables: for each day, the city visited
    day_city = [Int(f"day_{i}_city") for i in range(1, num_days + 1)]
    
    # Create a mapping from city names to integers
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    # Each day_city variable must be within 0..len(cities)-1
    for dc in day_city:
        s.add(And(dc >= 0, dc < len(cities)))
    
    # Add fixed events constraints
    for city, start_day, end_day in fixed_events:
        city_id = city_ids[city]
        for day in range(start_day, end_day + 1):
            s.add(day_city[day - 1] == city_id)
    
    # Constraints for the required number of days per city
    for city, req_days in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(day_city[i] == city_id, 1, 0) for i in range(num_days)) == req_days)
    
    # Flight constraints: consecutive days must be same city or connected by direct flight
    for i in range(num_days - 1):
        current_city = day_city[i]
        next_city = day_city[i + 1]
        # Either same city or connected by flight
        same_city = current_city == next_city
        flight_possible = False
        for city1 in cities:
            for city2 in cities:
                if city1 == city2:
                    continue
                if city2 in direct_flights.get(city1, []):
                    c1_id = city_ids[city1]
                    c2_id = city_ids[city2]
                    flight_possible = Or(flight_possible, And(current_city == c1_id, next_city == c2_id))
        s.add(Or(same_city, flight_possible))
    
    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        
        for day in range(1, num_days + 1):
            city_id = m.evaluate(day_city[day - 1]).as_long()
            city = id_to_city[city_id]
            
            if current_city is None:
                current_city = city
                start_day = day
            elif city != current_city:
                # Add the previous city's stay
                if start_day == day - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": current_city})
                # Add the flight day entries for both cities
                itinerary.append({"day_range": f"Day {day}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": city})
                current_city = city
                start_day = day
            # Handle the last day
            if day == num_days:
                if start_day == day:
                    itinerary.append({"day_range": f"Day {day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_city})
        
        # Verify that all cities have the required days
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            day_range = entry["day_range"]
            place = entry["place"]
            if '-' in day_range:
                start, end = map(int, day_range.replace("Day ", "").split('-'))
                days = end - start + 1
            else:
                days = 1
            city_days[place] += days
        
        for city in cities:
            assert city_days[city] == cities[city], f"City {city} has {city_days[city]} days instead of {cities[city]}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))