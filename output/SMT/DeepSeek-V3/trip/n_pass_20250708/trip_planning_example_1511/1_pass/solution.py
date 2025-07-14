from z3 import *
import json

def solve_scheduling_problem():
    # Define the cities and their required days
    cities = {
        "Venice": 3,
        "Reykjavik": 2,
        "Munich": 3,
        "Santorini": 3,
        "Manchester": 3,
        "Porto": 3,
        "Bucharest": 5,
        "Tallinn": 4,
        "Valencia": 2,
        "Vienna": 5
    }
    
    # Fixed constraints
    fixed_constraints = [
        ("Munich", 4, 6),
        ("Santorini", 8, 10),
        ("Valencia", 14, 15)
    ]
    
    # Direct flights
    direct_flights = {
        "Bucharest": ["Manchester", "Valencia", "Vienna", "Munich", "Santorini"],
        "Munich": ["Venice", "Porto", "Manchester", "Reykjavik", "Vienna", "Bucharest", "Tallinn", "Valencia"],
        "Santorini": ["Manchester", "Venice", "Vienna", "Bucharest"],
        "Vienna": ["Reykjavik", "Valencia", "Manchester", "Porto", "Venice", "Bucharest", "Santorini", "Munich"],
        "Venice": ["Munich", "Santorini", "Manchester", "Vienna"],
        "Manchester": ["Bucharest", "Santorini", "Vienna", "Porto", "Venice", "Munich"],
        "Porto": ["Munich", "Vienna", "Valencia", "Manchester"],
        "Valencia": ["Vienna", "Bucharest", "Porto", "Munich"],
        "Reykjavik": ["Vienna", "Munich"],
        "Tallinn": ["Munich"]
    }
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Create variables: for each day, which city are we in?
    days = 24
    day_to_city = [Int(f"day_{i}_city") for i in range(1, days + 1)]
    
    # Assign each city a unique integer
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Add constraints: each day's city must be one of the valid cities
    for day_var in day_to_city:
        solver.add(Or([day_var == city_ids[city] for city in cities.keys()]))
    
    # Fixed constraints
    for city, start, end in fixed_constraints:
        for day in range(start, end + 1):
            solver.add(day_to_city[day - 1] == city_ids[city])
    
    # Duration constraints: total days in each city must match the required duration
    for city, duration in cities.items():
        solver.add(Sum([If(day_to_city[i] == city_ids[city], 1, 0) for i in range(days)]) == duration
    
    # Flight constraints: consecutive days must be either the same city or have a direct flight
    for i in range(days - 1):
        current_city_var = day_to_city[i]
        next_city_var = day_to_city[i + 1]
        solver.add(
            Or(
                current_city_var == next_city_var,
                *[
                    And(current_city_var == city_ids[city1], next_city_var == city_ids[city2])
                    for city1 in direct_flights
                    for city2 in direct_flights[city1]
                ]
            )
        )
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        
        # Group consecutive days in the same city
        current_city = None
        start_day = 1
        for day in range(1, days + 1):
            city_id = model.evaluate(day_to_city[day - 1]).as_long()
            city = id_to_city[city_id]
            if current_city is None:
                current_city = city
                start_day = day
            elif city != current_city:
                # Add the stay in the previous city
                if start_day == day - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": current_city})
                # Add the flight day (same day for both departure and arrival)
                itinerary.append({"day_range": f"Day {day}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": city})
                current_city = city
                start_day = day
        # Add the last city
        if start_day == days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{days}", "place": current_city})
        
        # Prepare the JSON output
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

solve_scheduling_problem()