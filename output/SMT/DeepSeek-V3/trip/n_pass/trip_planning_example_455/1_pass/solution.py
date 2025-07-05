from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Reykjavik": 7,
        "Riga": 2,
        "Warsaw": 3,
        "Istanbul": 6,
        "Krakow": 7
    }
    
    # Direct flight connections
    direct_flights = [
        ("Istanbul", "Krakow"),
        ("Warsaw", "Reykjavik"),
        ("Istanbul", "Warsaw"),
        ("Riga", "Istanbul"),
        ("Krakow", "Warsaw"),
        ("Riga", "Warsaw")
    ]
    
    # Make the flights bidirectional
    bidirectional_flights = []
    for a, b in direct_flights:
        bidirectional_flights.append((a, b))
        bidirectional_flights.append((b, a))
    direct_flights = bidirectional_flights
    
    # Total days
    total_days = 21
    
    # Create a Z3 solver
    solver = Solver()
    
    # Variables: for each day (1..21), which city are we in?
    day_city = [Int(f"day_{day}_city") for day in range(1, total_days + 1)]
    
    # Assign each city a unique integer
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Constraint: each day's city must be one of the five cities
    for day in range(total_days):
        solver.add(Or([day_city[day] == city_ids[city] for city in cities]))
    
    # Constraint: transitions between cities must be via direct flights or staying
    for day in range(total_days - 1):
        current_city = day_city[day]
        next_city = day_city[day + 1]
        # Either stay in the same city or take a direct flight
        solver.add(Or(
            current_city == next_city,
            *[And(current_city == city_ids[a], next_city == city_ids[b]) for a, b in direct_flights]
        ))
    
    # Constraint: total days per city
    for city, days in cities.items():
        solver.add(Sum([If(day_city[day] == city_ids[city], 1, 0) for day in range(total_days)]) == days)
    
    # Constraint: wedding in Istanbul between day 2 and day 7 (i.e., must be in Istanbul at some point during days 3-7)
    # So Istanbul must include at least one day between day 3 and day 7 (1-based to 0-based: days 2-6)
    solver.add(Or([day_city[day] == city_ids["Istanbul"] for day in range(2, 7)]))
    
    # Constraint: meet friend in Riga between day 1 and day 2 (i.e., must be in Riga on day 1 or day 2)
    solver.add(Or(day_city[0] == city_ids["Riga"], day_city[1] == city_ids["Riga"]))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        
        # Determine the sequence of cities from the model
        sequence = []
        for day in range(total_days):
            city_id = model.evaluate(day_city[day]).as_long()
            sequence.append(id_to_city[city_id])
        
        # Generate day ranges for the itinerary
        current_place = sequence[0]
        start_day = 1
        for day in range(1, total_days):
            if sequence[day] != current_place:
                # Add the stay up to the previous day
                if start_day == day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_place})
                # Add the flight day entries (day is the transition day)
                itinerary.append({"day_range": f"Day {day}", "place": current_place})
                itinerary.append({"day_range": f"Day {day}", "place": sequence[day]})
                current_place = sequence[day]
                start_day = day + 1
        # Add the last stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))