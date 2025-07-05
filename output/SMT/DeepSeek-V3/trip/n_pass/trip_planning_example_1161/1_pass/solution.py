import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Mykonos": 4,
        "Krakow": 5,
        "Vilnius": 2,
        "Helsinki": 2,
        "Dubrovnik": 3,
        "Oslo": 2,
        "Madrid": 5,
        "Paris": 2
    }
    
    # Direct flight connections
    connections = {
        "Oslo": ["Krakow", "Paris", "Madrid", "Helsinki", "Dubrovnik", "Vilnius"],
        "Krakow": ["Oslo", "Paris", "Helsinki", "Vilnius"],
        "Paris": ["Oslo", "Madrid", "Krakow", "Helsinki", "Vilnius"],
        "Helsinki": ["Oslo", "Vilnius", "Krakow", "Dubrovnik", "Paris", "Madrid"],
        "Vilnius": ["Helsinki", "Oslo", "Krakow", "Paris"],
        "Dubrovnik": ["Helsinki", "Madrid", "Oslo"],
        "Madrid": ["Paris", "Oslo", "Helsinki", "Dubrovnik", "Mykonos"],
        "Mykonos": ["Madrid"]
    }
    
    total_days = 18
    days = list(range(1, total_days + 1))
    
    # Create a Z3 solver
    solver = Solver()
    
    # Variables: for each day, which city are we in?
    day_to_city = {day: Int(f"day_{day}") for day in days}
    
    # Assign each day's city to a numeric value representing the city
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Add constraints: each day's city must be one of the cities
    for day in days:
        solver.add(Or([day_to_city[day] == city_ids[city] for city in cities]))
    
    # Constraints on consecutive days: must be connected by a direct flight
    for day in days[:-1]:
        current_day_city = day_to_city[day]
        next_day_city = day_to_city[day + 1]
        # Either stay in the same city or move to a connected city
        solver.add(Or(
            current_day_city == next_day_city,
            *[
                And(current_day_city == city_ids[city1], next_day_city == city_ids[city2])
                for city1 in cities
                for city2 in connections.get(city1, [])
            ]
        ))
    
    # Constraints on total days per city
    for city in cities:
        count = Sum([If(day_to_city[day] == city_ids[city], 1, 0) for day in days])
        solver.add(count == cities[city])
    
    # Specific constraints:
    # Mykonos between day 15-18 (inclusive)
    for day in range(15, 19):
        solver.add(day_to_city[day] == city_ids["Mykonos"])
    
    # Dubrovnik from day 2-4 (inclusive)
    for day in range(2, 5):
        solver.add(day_to_city[day] == city_ids["Dubrovnik"])
    
    # Oslo between day 1-2 (inclusive)
    for day in range(1, 3):
        solver.add(day_to_city[day] == city_ids["Oslo"])
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        # Extract the itinerary
        itinerary_days = []
        for day in days:
            city_id = model.evaluate(day_to_city[day]).as_long()
            itinerary_days.append(id_to_city[city_id])
        
        # Now, generate the itinerary in the required format
        itinerary = []
        current_place = itinerary_days[0]
        start_day = 1
        
        for day in range(1, len(itinerary_days)):
            if itinerary_days[day] != current_place:
                # Add the stay up to the previous day
                if start_day == day:
                    day_str = f"Day {start_day}"
                else:
                    day_str = f"Day {start_day}-{day}"
                itinerary.append({"day_range": day_str, "place": current_place})
                # Add the flight day entries for both departure and arrival
                itinerary.append({"day_range": f"Day {day}", "place": current_place})
                itinerary.append({"day_range": f"Day {day}", "place": itinerary_days[day]})
                current_place = itinerary_days[day]
                start_day = day + 1
            # else: continue the stay
        
        # Add the last stay
        if start_day == total_days:
            day_str = f"Day {start_day}"
        else:
            day_str = f"Day {start_day}-{total_days}"
        itinerary.append({"day_range": day_str, "place": current_place})
        
        # Verify the itinerary meets all constraints
        # (Debugging step: ensure the itinerary is correct)
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))