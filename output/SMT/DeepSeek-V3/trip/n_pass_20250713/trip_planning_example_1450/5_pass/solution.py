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
    
    # Direct flights (bidirectional)
    flights = {
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

    # Initialize assignments with fixed constraints
    assignments = [None]*32
    for day in range(25, 30):
        assignments[day-1] = "Istanbul"
    for day in range(5, 10):
        assignments[day-1] = "Krakow"

    # Create solver
    solver = Solver()

    # Variables for remaining days
    remaining_days = [i for i in range(32) if assignments[i] is None]
    day_vars = [Int(f"day_{i+1}") for i in remaining_days]
    
    # City mapping
    city_names = sorted(cities.keys())
    city_to_int = {city: idx for idx, city in enumerate(city_names)}
    int_to_city = {idx: city for idx, city in enumerate(city_names)}

    # Constraints for remaining days
    for day_var in day_vars:
        solver.add(Or([day_var == city_to_int[city] for city in city_names]))

    # Count days per city (subtract fixed days)
    city_counts = cities.copy()
    city_counts["Istanbul"] -= 5
    city_counts["Krakow"] -= 5
    for city, count in city_counts.items():
        solver.add(Sum([If(day_var == city_to_int[city], 1, 0) for day_var in day_vars]) == count)

    # Flight constraints between consecutive days
    all_days = assignments.copy()
    for i, day_var in zip(remaining_days, day_vars):
        all_days[i] = day_var

    for i in range(31):
        current = all_days[i]
        next_day = all_days[i+1]
        if isinstance(current, str) and isinstance(next_day, str):
            if current != next_day and next_day not in flights[current]:
                solver.add(False)  # Invalid connection
        elif isinstance(current, str):
            solver.add(Or(next_day == city_to_int[current], 
                         *[next_day == city_to_int[c] for c in flights[current]]))
        elif isinstance(next_day, str):
            solver.add(Or(current == city_to_int[next_day],
                      *[current == city_to_int[c] for c in flights[next_day]]))
        else:
            same_city = current == next_day
            connected = []
            for city in city_names:
                connected += [And(current == city_to_int[city], 
                              next_day == city_to_int[c]) for c in flights[city]]
            solver.add(Or(same_city, *connected))

    if solver.check() == sat:
        model = solver.model()
        # Fill in remaining assignments
        for i, day_var in zip(remaining_days, day_vars):
            assignments[i] = int_to_city[model.evaluate(day_var).as_long()]

        # Build itinerary
        itinerary = []
        current = assignments[0]
        start = 1
        for i in range(1, 32):
            if assignments[i] != current:
                end = i
                if start == end:
                    itinerary.append({"day_range": f"Day {start}", "place": current})
                else:
                    itinerary.append({"day_range": f"Day {start}-{end}", "place": current})
                itinerary.append({"day_range": f"Day {i}", "place": current})
                itinerary.append({"day_range": f"Day {i}", "place": assignments[i]})
                current = assignments[i]
                start = i + 1
        if start <= 32:
            if start == 32:
                itinerary.append({"day_range": f"Day {start}", "place": current})
            else:
                itinerary.append({"day_range": f"Day {start}-32", "place": current})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))