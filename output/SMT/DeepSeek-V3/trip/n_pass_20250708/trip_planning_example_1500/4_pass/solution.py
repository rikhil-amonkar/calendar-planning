from z3 import *
import json

def solve_itinerary():
    # Cities to visit
    cities = ["London", "Zurich", "Bucharest", "Hamburg", "Barcelona", "Reykjavik", "Stuttgart", "Stockholm", "Tallinn", "Milan"]
    
    # Direct flights as tuples (from, to)
    direct_flights = [
        ("London", "Hamburg"), ("London", "Reykjavik"), ("Milan", "Barcelona"), ("Reykjavik", "Barcelona"),
        ("Reykjavik", "Stuttgart"), ("Stockholm", "Reykjavik"), ("London", "Stuttgart"), ("Milan", "Zurich"),
        ("London", "Barcelona"), ("Stockholm", "Hamburg"), ("Zurich", "Barcelona"), ("Stockholm", "Stuttgart"),
        ("Milan", "Hamburg"), ("Stockholm", "Tallinn"), ("Hamburg", "Bucharest"), ("London", "Bucharest"),
        ("Milan", "Stockholm"), ("Stuttgart", "Hamburg"), ("London", "Zurich"), ("Milan", "Reykjavik"),
        ("London", "Stockholm"), ("Milan", "Stuttgart"), ("Stockholm", "Barcelona"), ("London", "Milan"),
        ("Zurich", "Hamburg"), ("Bucharest", "Barcelona"), ("Zurich", "Stockholm"), ("Barcelona", "Tallinn"),
        ("Zurich", "Tallinn"), ("Hamburg", "Barcelona"), ("Stuttgart", "Barcelona"), ("Zurich", "Reykjavik"),
        ("Zurich", "Bucharest")
    ]
    
    # Create a dictionary of direct flight connections for quick lookup
    flight_connections = {city: set() for city in cities}
    for from_city, to_city in direct_flights:
        flight_connections[from_city].add(to_city)
        flight_connections[to_city].add(from_city)
    
    # Required days per city
    required_days = {
        "London": 3,
        "Zurich": 2,
        "Bucharest": 2,
        "Hamburg": 5,
        "Barcelona": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Stockholm": 2,
        "Tallinn": 4,
        "Milan": 5
    }
    
    # Fixed constraints
    fixed_days = [
        ("London", 1, 3),
        ("Milan", 3, 7),
        ("Zurich", 7, 8),
        ("Reykjavik", 9, 13)
    ]
    
    # Initialize Z3 variables
    s = Solver()
    day_to_city = {day: Int(f"day_{day}") for day in range(1, 29)}  # 1-based
    
    # Assign each day to a city (encoded as integers)
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    for day in range(1, 29):
        s.add(day_to_city[day] >= 0, day_to_city[day] < len(cities))
    
    # Apply fixed constraints
    for city, start_day, end_day in fixed_days:
        city_code = city_to_int[city]
        for day in range(start_day, end_day + 1):
            s.add(day_to_city[day] == city_code)
    
    # Ensure transitions are via direct flights
    for day in range(1, 28):
        current_city = day_to_city[day]
        next_city = day_to_city[day + 1]
        # Either stay in the same city or move to a connected city
        possible_transitions = []
        for from_city in cities:
            for to_city in flight_connections[from_city]:
                possible_transitions.append(And(current_city == city_to_int[from_city], next_city == city_to_int[to_city]))
        s.add(Or(current_city == next_city, Or(possible_transitions)))
    
    # Ensure total days per city
    for city in cities:
        city_code = city_to_int[city]
        total_days = Sum([If(day_to_city[day] == city_code, 1, 0) for day in range(1, 29)])
        s.add(total_days == required_days[city])
    
    # Check for model and print itinerary
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_place = None
        start_day = 1
        
        for day in range(1, 29):
            city_code = model.evaluate(day_to_city[day]).as_long()
            city = int_to_city[city_code]
            
            if day == 1:
                current_place = city
                start_day = 1
            else:
                prev_city_code = model.evaluate(day_to_city[day - 1]).as_long()
                prev_city = int_to_city[prev_city_code]
                
                if city != prev_city:
                    # Add the previous stay
                    if start_day == day - 1:
                        itinerary.append({"day_range": f"Day {start_day}", "place": prev_city})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": prev_city})
                    # Add the flight day for previous city
                    itinerary.append({"day_range": f"Day {day}", "place": prev_city})
                    # Add the flight day for current city
                    itinerary.append({"day_range": f"Day {day}", "place": city})
                    current_place = city
                    start_day = day
        
        # Add the last stay
        if start_day == 28:
            itinerary.append({"day_range": f"Day {28}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{28}", "place": current_place})
        
        # Verify that all required cities are covered
        covered_cities = set([entry["place"] for entry in itinerary])
        if covered_cities != set(cities):
            print("Error: Not all cities are covered in the itinerary.")
            return None
        
        return {"itinerary": itinerary}
    else:
        print("No solution found.")
        return None

solution = solve_itinerary()
if solution:
    print(json.dumps(solution, indent=2))