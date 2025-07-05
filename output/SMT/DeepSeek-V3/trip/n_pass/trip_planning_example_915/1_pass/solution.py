from z3 import *
import json

def solve_itinerary():
    # Cities to visit
    cities = ["Bucharest", "Venice", "Prague", "Frankfurt", "Zurich", "Florence", "Tallinn"]
    
    # Total days
    total_days = 26
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Variables: for each day, which city are we in?
    # We represent days as 1..26
    day_city = [Int(f"day_{i}_city") for i in range(1, total_days + 1)]
    
    # Each day_city variable must be an index corresponding to a city (0..6)
    for day in range(total_days):
        solver.add(day_city[day] >= 0, day_city[day] < len(cities))
    
    # Flight connections (direct flights between cities)
    # Represented as a set of tuples (city_index1, city_index2)
    connections = [
        (cities.index("Prague"), cities.index("Tallinn")),
        (cities.index("Prague"), cities.index("Zurich")),
        (cities.index("Florence"), cities.index("Prague")),
        (cities.index("Frankfurt"), cities.index("Bucharest")),
        (cities.index("Frankfurt"), cities.index("Venice")),
        (cities.index("Prague"), cities.index("Bucharest")),
        (cities.index("Bucharest"), cities.index("Zurich")),
        (cities.index("Tallinn"), cities.index("Frankfurt")),
        (cities.index("Zurich"), cities.index("Florence")),
        (cities.index("Frankfurt"), cities.index("Zurich")),
        (cities.index("Zurich"), cities.index("Venice")),
        (cities.index("Florence"), cities.index("Frankfurt")),
        (cities.index("Prague"), cities.index("Frankfurt")),
        (cities.index("Tallinn"), cities.index("Zurich"))
    ]
    
    # Ensure that consecutive days are either the same city or connected by a direct flight
    for i in range(total_days - 1):
        current_city = day_city[i]
        next_city = day_city[i + 1]
        # Either stay in the same city or move to a connected city
        solver.add(Or(
            current_city == next_city,
            Or([And(current_city == c1, next_city == c2) for c1, c2 in connections])
        ))
    
    # Constraints for each city's stay duration
    # Bucharest: 3 days
    solver.add(Sum([If(day_city[i] == cities.index("Bucharest"), 1, 0) for i in range(total_days)]) == 3)
    # Venice: 5 days, with days 22-26 in Venice (indices 21-25 in 0-based)
    solver.add(Sum([If(day_city[i] == cities.index("Venice"), 1, 0) for i in range(21, 26)]) == 5)
    # Prague: 4 days
    solver.add(Sum([If(day_city[i] == cities.index("Prague"), 1, 0) for i in range(total_days)]) == 4)
    # Frankfurt: 5 days, with days 12-16 in Frankfurt (indices 11-15)
    solver.add(Sum([If(day_city[i] == cities.index("Frankfurt"), 1, 0) for i in range(11, 16)]) == 5)
    # Zurich: 5 days
    solver.add(Sum([If(day_city[i] == cities.index("Zurich"), 1, 0) for i in range(total_days)]) == 5)
    # Florence: 5 days
    solver.add(Sum([If(day_city[i] == cities.index("Florence"), 1, 0) for i in range(total_days)]) == 5)
    # Tallinn: 5 days, with days 8-12 in Tallinn (indices 7-11)
    solver.add(Sum([If(day_city[i] == cities.index("Tallinn"), 1, 0) for i in range(7, 12)]) == 5)
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        
        # Generate the day sequence
        day_sequence = []
        for i in range(total_days):
            city_idx = model.evaluate(day_city[i]).as_long()
            day_sequence.append(cities[city_idx])
        
        # Process the day sequence to create the itinerary with ranges
        current_place = day_sequence[0]
        start_day = 1
        for i in range(1, total_days):
            if day_sequence[i] != current_place:
                # Add the stay up to previous day
                if start_day == i:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_place})
                # Add the transition day (same day for both departure and arrival)
                itinerary.append({"day_range": f"Day {i}", "place": current_place})
                itinerary.append({"day_range": f"Day {i}", "place": day_sequence[i]})
                current_place = day_sequence[i]
                start_day = i + 1
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