from z3 import *
import json

def solve_itinerary():
    # Cities to visit
    cities = ["London", "Zurich", "Bucharest", "Hamburg", "Barcelona", "Reykjavik", "Stuttgart", "Stockholm", "Tallinn", "Milan"]
    
    # Direct flights (bidirectional)
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
    
    # Create flight connections dictionary
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

    # Fixed constraints (city, start_day, end_day)
    fixed_periods = [
        ("London", 1, 3),
        ("Milan", 3, 7),
        ("Zurich", 7, 8),
        ("Reykjavik", 9, 13)
    ]

    # Initialize Z3 solver
    s = Solver()
    
    # Create variables for each day (1-28)
    day_to_city = [Int(f"day_{i}") for i in range(1, 29)]
    
    # City to integer mapping
    city_to_int = {city: i for i, city in enumerate(cities)}
    int_to_city = {i: city for i, city in enumerate(cities)}

    # Apply fixed constraints first
    for city, start, end in fixed_periods:
        for day in range(start-1, end):  # 0-based indexing
            s.add(day_to_city[day] == city_to_int[city])

    # Assign remaining days (14-28) to other cities
    remaining_cities = [c for c in cities if c not in ["London", "Milan", "Zurich", "Reykjavik"]]
    for day in range(13, 28):  # Days after Reykjavik
        s.add(Or([day_to_city[day] == city_to_int[c] for c in remaining_cities]))

    # Ensure flight connections between consecutive days
    for day in range(27):  # Check transitions between days
        current = day_to_city[day]
        next_day = day_to_city[day+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            # Or fly to connected city
            Or([And(current == city_to_int[from_c], next_day == city_to_int[to_c])
                for from_c in cities for to_c in flight_connections[from_c]])
        ))

    # Ensure required days for each city
    for city in cities:
        count = Sum([If(day_to_city[i] == city_to_int[city], 1, 0) for i in range(28)])
        s.add(count == required_days[city])

    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Build itinerary from model
        current_city = None
        start_day = 1
        
        for day in range(28):
            city_idx = model.evaluate(day_to_city[day]).as_long()
            city = int_to_city[city_idx]
            
            if day == 0:
                current_city = city
                start_day = 1
            else:
                prev_city_idx = model.evaluate(day_to_city[day-1]).as_long()
                prev_city = int_to_city[prev_city_idx]
                
                if city != prev_city:
                    # Add previous stay
                    if start_day == day:
                        itinerary.append({"day_range": f"Day {start_day}", "place": prev_city})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day}", "place": prev_city})
                    # Add flight day
                    itinerary.append({"day_range": f"Day {day+1}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {day+1}", "place": city})
                    current_city = city
                    start_day = day + 1
        
        # Add last stay
        if start_day == 28:
            itinerary.append({"day_range": f"Day 28", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-28", "place": current_city})

        # Verify all cities are covered
        covered = set([x["place"] for x in itinerary])
        if covered == set(cities):
            return {"itinerary": itinerary}
    
    print("No valid itinerary found that satisfies all constraints")
    return None

solution = solve_itinerary()
if solution:
    print(json.dumps(solution, indent=2))