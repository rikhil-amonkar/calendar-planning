from z3 import *
import json

def solve_itinerary_with_z3():
    # Cities and their required days
    cities = {
        "Copenhagen": 5,
        "Geneva": 3,
        "Mykonos": 2,
        "Naples": 4,
        "Prague": 2,
        "Dubrovnik": 3,
        "Athens": 4,
        "Santorini": 5,
        "Brussels": 4,
        "Munich": 5
    }
    
    # Direct flights (bidirectional)
    direct_flights = [
        ("Copenhagen", "Dubrovnik"),
        ("Copenhagen", "Brussels"),
        ("Copenhagen", "Prague"),
        ("Copenhagen", "Naples"),
        ("Copenhagen", "Munich"),
        ("Copenhagen", "Geneva"),
        ("Copenhagen", "Santorini"),
        ("Copenhagen", "Athens"),
        ("Brussels", "Naples"),
        ("Brussels", "Munich"),
        ("Brussels", "Prague"),
        ("Brussels", "Athens"),
        ("Brussels", "Geneva"),
        ("Prague", "Geneva"),
        ("Prague", "Athens"),
        ("Prague", "Munich"),
        ("Geneva", "Athens"),
        ("Geneva", "Mykonos"),
        ("Geneva", "Munich"),
        ("Geneva", "Dubrovnik"),
        ("Geneva", "Santorini"),
        ("Athens", "Dubrovnik"),
        ("Athens", "Mykonos"),
        ("Athens", "Santorini"),
        ("Athens", "Naples"),
        ("Athens", "Munich"),
        ("Naples", "Dubrovnik"),
        ("Naples", "Mykonos"),
        ("Naples", "Munich"),
        ("Naples", "Geneva"),
        ("Naples", "Santorini"),
        ("Dubrovnik", "Munich"),
        ("Mykonos", "Munich"),
        ("Santorini", "Naples")
    ]
    
    # Make sure all flights are bidirectional
    bidirectional_flights = set()
    for a, b in direct_flights:
        bidirectional_flights.add((a, b))
        bidirectional_flights.add((b, a))
    direct_flights = bidirectional_flights
    
    total_days = 28
    city_names = list(cities.keys())
    num_cities = len(city_names)
    
    # Create Z3 variables for each day's city
    day_city = [Int(f"day_{i}_city") for i in range(total_days)]
    
    # Each day_city is an index into city_names
    solver = Solver()
    for dc in day_city:
        solver.add(And(dc >= 0, dc < num_cities))
    
    # Constraint: each city's total days must match the required days
    for city_idx in range(num_cities):
        city = city_names[city_idx]
        required_days = cities[city]
        solver.add(Sum([If(day_city[i] == city_idx, 1, 0) for i in range(total_days)]) == required_days)
    
    # Constraint: consecutive days in the same city or connected by flights
    for i in range(total_days - 1):
        current_city_idx = day_city[i]
        next_city_idx = day_city[i+1]
        solver.add(Or(
            current_city_idx == next_city_idx,
            And(current_city_idx != next_city_idx,
                Or([And(current_city_idx == city_names.index(a), next_city_idx == city_names.index(b)) for a, b in direct_flights]))
        ))
    
    # Specific constraints:
    # Copenhagen between day 11-15 (1-based to 0-based: days 10-14)
    solver.add(Or([day_city[i] == city_names.index("Copenhagen") for i in range(10, 15)]))
    # Mykonos conference on day 27-28 (0-based: 26-27)
    solver.add(day_city[26] == city_names.index("Mykonos"))
    solver.add(day_city[27] == city_names.index("Mykonos"))
    # Naples relatives between day 5-8 (0-based: 4-7)
    solver.add(Or([day_city[i] == city_names.index("Naples") for i in range(4, 8)]))
    # Athens workshop between day 8-11 (0-based: 7-10)
    solver.add(Or([day_city[i] == city_names.index("Athens") for i in range(7, 11)]))
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        current_city = None
        start_day = 0
        for day in range(total_days):
            city_idx = model.evaluate(day_city[day]).as_long()
            city = city_names[city_idx]
            if city != current_city:
                if current_city is not None:
                    # Add the previous city's stay
                    itinerary.append({
                        "day_range": f"Day {start_day+1}-{day}",
                        "place": current_city
                    })
                # Add the flight day entries
                if day != 0:
                    itinerary.append({
                        "day_range": f"Day {day}",
                        "place": current_city
                    })
                    itinerary.append({
                        "day_range": f"Day {day}",
                        "place": city
                    })
                current_city = city
                start_day = day
        # Add the last city's stay
        itinerary.append({
            "day_range": f"Day {start_day+1}-{total_days}",
            "place": current_city
        })
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary_with_z3()
print(json.dumps(result, indent=2))