from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Stockholm": 3,
        "Hamburg": 5,
        "Florence": 2,
        "Istanbul": 5,
        "Oslo": 5,
        "Vilnius": 5,
        "Santorini": 2,
        "Munich": 5,
        "Frankfurt": 4,
        "Krakow": 5
    }
    
    # Direct flights as a dictionary: city -> list of connected cities
    direct_flights = {
        "Oslo": ["Stockholm", "Istanbul", "Krakow", "Vilnius", "Frankfurt", "Munich", "Hamburg"],
        "Stockholm": ["Oslo", "Munich", "Hamburg", "Istanbul", "Frankfurt", "Santorini", "Krakow"],
        "Krakow": ["Frankfurt", "Istanbul", "Vilnius", "Oslo", "Munich", "Stockholm"],
        "Frankfurt": ["Krakow", "Istanbul", "Oslo", "Florence", "Stockholm", "Munich", "Hamburg", "Vilnius"],
        "Munich": ["Stockholm", "Hamburg", "Istanbul", "Oslo", "Frankfurt", "Florence", "Krakow", "Vilnius"],
        "Hamburg": ["Stockholm", "Munich", "Istanbul", "Oslo", "Frankfurt"],
        "Istanbul": ["Krakow", "Oslo", "Stockholm", "Vilnius", "Frankfurt", "Munich", "Hamburg"],
        "Vilnius": ["Krakow", "Istanbul", "Oslo", "Frankfurt", "Munich"],
        "Florence": ["Frankfurt", "Munich"],
        "Santorini": ["Stockholm", "Oslo"]
    }
    
    # Ensure all cities are in the direct_flights
    for city in cities:
        if city not in direct_flights:
            direct_flights[city] = []
    
    # Build a bidirectional flights graph
    bidirectional_flights = {}
    for city in direct_flights:
        bidirectional_flights[city] = set(direct_flights[city])
    
    for city in direct_flights:
        for connected in direct_flights[city]:
            if connected not in bidirectional_flights:
                bidirectional_flights[connected] = set()
            bidirectional_flights[connected].add(city)
    
    # Create a Z3 solver
    solver = Solver()
    
    # Days are 1..32
    Day = 32
    
    # Create variables for each day: day_1, day_2, ..., day_32
    day_vars = [Int(f"day_{i}") for i in range(1, Day + 1)]
    
    # Create a mapping from city names to integers
    city_names = sorted(cities.keys())
    city_to_int = {city: idx for idx, city in enumerate(city_names)}
    int_to_city = {idx: city for idx, city in enumerate(city_names)}
    
    # Constraint: each day_var must be one of the city integers
    for day_var in day_vars:
        solver.add(Or([day_var == city_to_int[city] for city in city_names]))
    
    # Constraint: total days in each city must match the required days
    for city, required_days in cities.items():
        city_int = city_to_int[city]
        solver.add(Sum([If(day_var == city_int, 1, 0) for day_var in day_vars]) == required_days)
    
    # Special constraints:
    # Istanbul from day 25 to 29 (inclusive)
    for day in range(25, 30):
        solver.add(day_vars[day - 1] == city_to_int["Istanbul"])
    
    # Workshop in Krakow between day 5 and day 9 (inclusive)
    for day in range(5, 10):
        solver.add(day_vars[day - 1] == city_to_int["Krakow"])
    
    # Flight constraints: consecutive days must be either the same city or connected by a direct flight
    for i in range(Day - 1):
        current_day_var = day_vars[i]
        next_day_var = day_vars[i + 1]
        current_city = int_to_city[model.evaluate(current_day_var).as_long()] if i > 0 else int_to_city[0]
        next_city = int_to_city[model.evaluate(next_day_var).as_long()]
        
        # Either stay in the same city or move to a connected city
        solver.add(Or(
            current_day_var == next_day_var,
            And(
                current_day_var != next_day_var,
                next_city in bidirectional_flights.get(int_to_city[model.evaluate(current_day_var).as_long()], [])
            ))
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        
        # Extract the day assignments
        day_assignments = []
        for i in range(Day):
            day_var = day_vars[i]
            city_int = model.evaluate(day_var).as_long()
            city = int_to_city[city_int]
            day_assignments.append(city)
        
        # Process the day assignments to create the itinerary with flight days
        current_place = day_assignments[0]
        start_day = 1
        for i in range(1, Day):
            if day_assignments[i] != current_place:
                # Flight day: day i+1 is the transition day
                end_day = i
                if start_day == end_day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_place})
                # Add the flight day entries for both cities
                itinerary.append({"day_range": f"Day {i}", "place": current_place})
                itinerary.append({"day_range": f"Day {i}", "place": day_assignments[i]})
                current_place = day_assignments[i]
                start_day = i + 1
            # else: continue the stay
        
        # Add the last stay
        if start_day <= Day:
            if start_day == Day:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{Day}", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))