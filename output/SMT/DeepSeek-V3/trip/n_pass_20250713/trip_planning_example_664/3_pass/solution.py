from z3 import *
import json

def solve_itinerary():
    # Cities and their required stay days
    cities = {
        "Tallinn": 2,
        "Bucharest": 4,
        "Seville": 5,
        "Stockholm": 5,
        "Munich": 5,
        "Milan": 2
    }
    
    # Direct flights as adjacency list (bidirectional)
    flights = {
        "Milan": ["Stockholm", "Munich", "Seville"],
        "Stockholm": ["Milan", "Munich", "Tallinn"],
        "Munich": ["Stockholm", "Bucharest", "Seville", "Milan", "Tallinn"],
        "Bucharest": ["Munich"],
        "Seville": ["Munich", "Milan"],
        "Tallinn": ["Stockholm", "Munich"]
    }
    
    # Total days
    total_days = 18
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Create variables: day[i] represents the city on day i (1-based)
    day = [Int(f"day_{i}") for i in range(1, total_days + 1)]
    
    # Assign each day variable to a city code (we'll map cities to integers)
    city_map = {city: idx for idx, city in enumerate(cities.keys())}
    city_inv_map = {idx: city for city, idx in city_map.items()}
    
    # Add constraints that each day variable is within the city codes
    for d in day:
        solver.add(d >= 0, d < len(cities))
    
    # Constraint: total days per city must match the required stay
    for city, stay in cities.items():
        city_code = city_map[city]
        solver.add(Sum([If(d == city_code, 1, 0) for d in day]) == stay)
    
    # Event constraints:
    # Bucharest between day 1-4 (at least one day in 1-4 is Bucharest)
    solver.add(Or([day[i] == city_map["Bucharest"] for i in range(0, 4)]))
    
    # Munich wedding between day 4-8 (days 5-8 in 1-based is indices 4-7)
    solver.add(Or([day[i] == city_map["Munich"] for i in range(4, 8)]))
    
    # Seville friends between day 8-12 (indices 7-11 in 0-based)
    solver.add(Or([day[i] == city_map["Seville"] for i in range(7, 12)]))
    
    # Flight transitions: consecutive days must be connected by a direct flight or same city
    for i in range(total_days - 1):
        current_city = day[i]
        next_city = day[i+1]
        # Either stay in the same city or move to a connected city
        solver.add(
            Or(
                current_city == next_city,
                *[
                    And(current_city == city_map[c1], next_city == city_map[c2])
                    for c1 in flights
                    for c2 in flights[c1]
                ]
            )
        )
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        decoded_days = [city_inv_map[model.evaluate(day[i]).as_long()] for i in range(total_days)]
        
        # Generate the itinerary
        itinerary = []
        current_place = decoded_days[0]
        start_day = 1
        
        for i in range(1, total_days):
            if decoded_days[i] == decoded_days[i-1]:
                continue
            else:
                # Flight from decoded_days[i-1] to decoded_days[i] on day i+1 (1-based)
                end_day = i  # 0-based, so day i+1 is the flight day in 1-based
                if start_day <= end_day:
                    day_str = f"Day {start_day}-{end_day + 1}" if start_day != end_day + 1 else f"Day {start_day}"
                    itinerary.append({"day_range": day_str, "place": current_place})
                # Add flight day entries
                flight_day = i + 1  # 1-based
                itinerary.append({"day_range": f"Day {flight_day}", "place": current_place})
                itinerary.append({"day_range": f"Day {flight_day}", "place": decoded_days[i]})
                current_place = decoded_days[i]
                start_day = flight_day + 1
        
        # Add the last segment
        if start_day <= total_days:
            day_str = f"Day {start_day}-{total_days}" if start_day != total_days else f"Day {start_day}"
            itinerary.append({"day_range": day_str, "place": current_place})
        
        # Verify the itinerary meets all constraints
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
        
        valid = all(city_days[city] == cities[city] for city in cities)
        if valid:
            return {"itinerary": itinerary}
        else:
            # Fallback: return the basic itinerary without flight day splits
            basic_itinerary = []
            current_place = decoded_days[0]
            start_day = 1
            for i in range(1, total_days + 1):
                if i == total_days or decoded_days[i] != decoded_days[i-1]:
                    end_day = i
                    day_str = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
                    basic_itinerary.append({"day_range": day_str, "place": current_place})
                    if i < total_days:
                        current_place = decoded_days[i]
                        start_day = i + 1
            return {"itinerary": basic_itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the function and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))