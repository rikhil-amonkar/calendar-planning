from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Helsinki": 4,
        "Valencia": 5,
        "Dubrovnik": 4,
        "Porto": 3,
        "Prague": 3,
        "Reykjavik": 4
    }
    city_list = list(cities.keys())
    
    # Direct flights as adjacency list
    flights = {
        "Helsinki": ["Prague", "Reykjavik", "Dubrovnik"],
        "Prague": ["Helsinki", "Valencia", "Reykjavik"],
        "Valencia": ["Prague", "Porto"],
        "Porto": ["Valencia"],
        "Reykjavik": ["Helsinki", "Prague"],
        "Dubrovnik": ["Helsinki"]
    }
    
    # Create a Z3 solver instance
    s = Solver()
    
    # Create variables: each day is assigned to a city
    days = 18
    assignments = [Int(f"day_{i}") for i in range(1, days + 1)]
    
    # Each day's assignment must be between 0 and 5 (indices of city_list)
    for day in assignments:
        s.add(day >= 0, day < len(city_list))
    
    # Constraint: consecutive cities must have a direct flight
    for i in range(days - 1):
        current_city = assignments[i]
        next_city = assignments[i + 1]
        # For each possible current city, next city must be in its flight list
        for city_idx in range(len(city_list)):
            city = city_list[city_idx]
            allowed_next = [city_list.index(c) for c in flights[city]]
            s.add(Implies(current_city == city_idx, Or([next_city == idx for idx in allowed_next])))
    
    # Constraint: total days per city must match requirements
    for city_idx in range(len(city_list)):
        city = city_list[city_idx]
        required_days = cities[city]
        # Count occurrences of the city in assignments
        total = 0
        for day in assignments:
            total += If(day == city_idx, 1, 0)
        s.add(total == required_days)
    
    # Constraint: Porto must be visited between day 16 and 18 (inclusive)
    porto_idx = city_list.index("Porto")
    s.add(Or([assignments[i] == porto_idx for i in range(15, 18)]))  # days are 1-based in problem, 0-based here
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        # Decode the model into the itinerary
        for i in range(days):
            city_idx = model.evaluate(assignments[i]).as_long()
            itinerary.append({"day": i + 1, "place": city_list[city_idx]})
        
        # Verify the solution meets all constraints (sanity check)
        # Check city days
        city_days = {city: 0 for city in city_list}
        for entry in itinerary:
            city_days[entry["place"]] += 1
        for city in cities:
            assert city_days[city] == cities[city], f"City {city} has {city_days[city]} days instead of {cities[city]}"
        
        # Check flight connections
        for i in range(len(itinerary) - 1):
            current = itinerary[i]["place"]
            next_place = itinerary[i + 1]["place"]
            assert next_place in flights[current], f"No flight from {current} to {next_place}"
        
        # Check Porto days
        porto_days = [entry["day"] for entry in itinerary if entry["place"] == "Porto"]
        assert any(16 <= day <= 18 for day in porto_days), "Porto not visited between day 16 and 18"
        
        # Format the output as JSON
        output = {"itinerary": itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))