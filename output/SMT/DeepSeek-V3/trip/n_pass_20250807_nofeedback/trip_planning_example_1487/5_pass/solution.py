from z3 import *

def solve_itinerary():
    # Cities
    cities = [
        "Copenhagen",
        "Geneva",
        "Mykonos",
        "Naples",
        "Prague",
        "Dubrovnik",
        "Athens",
        "Santorini",
        "Brussels",
        "Munich"
    ]
    
    # Direct flights (corrected for typos)
    direct_flights = {
        "Copenhagen": ["Dubrovnik", "Brussels", "Prague", "Naples", "Munich", "Geneva", "Athens", "Santorini"],
        "Geneva": ["Prague", "Athens", "Mykonos", "Santorini", "Naples", "Dubrovnik", "Munich", "Brussels", "Copenhagen"],
        "Mykonos": ["Geneva", "Naples", "Athens", "Munich"],
        "Naples": ["Dubrovnik", "Mykonos", "Copenhagen", "Athens", "Munich", "Geneva", "Santorini"],
        "Prague": ["Geneva", "Athens", "Brussels", "Copenhagen", "Munich"],
        "Dubrovnik": ["Copenhagen", "Naples", "Athens", "Munich", "Geneva"],
        "Athens": ["Geneva", "Dubrovnik", "Mykonos", "Naples", "Prague", "Santorini", "Brussels", "Munich", "Copenhagen"],
        "Santorini": ["Geneva", "Athens", "Copenhagen", "Naples"],
        "Brussels": ["Copenhagen", "Naples", "Prague", "Munich", "Athens", "Geneva"],
        "Munich": ["Mykonos", "Naples", "Dubrovnik", "Brussels", "Athens", "Geneva", "Copenhagen", "Prague"]
    }
    
    # Duration constraints
    durations = {
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
    
    # Time window constraints
    time_windows = {
        "Copenhagen": (11, 15),  # Must be in Copenhagen between day 11 and day 15 (inclusive)
        "Naples": (5, 8),        # Must be in Naples between day 5 and day 8
        "Athens": (8, 11),       # Must be in Athens between day 8 and day 11
        "Mykonos": (27, 28)      # Must be in Mykonos on day 27 and 28
    }
    
    # Initialize Z3 solver
    s = Solver()
    
    # Create variables: assign a city to each day (1-based)
    day_to_city = [Int(f"day_{i}") for i in range(1, 29)]
    
    # Map each city to an integer
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Add constraints: each day's variable must be a valid city index
    for day in day_to_city:
        s.add(day >= 0, day < len(cities))
    
    # Duration constraints: each city must be visited for exactly the specified number of days
    for city in cities:
        count = Sum([If(day == city_to_int[city], 1, 0) for day in day_to_city])
        s.add(count == durations[city])
    
    # Time window constraints
    # Copenhagen between day 11 and 15 (inclusive)
    s.add(Or([day_to_city[i] == city_to_int["Copenhagen"] for i in range(10, 15)]))  # days 11-15 are indices 10-14
    
    # Naples between day 5 and 8
    s.add(Or([day_to_city[i] == city_to_int["Naples"] for i in range(4, 8)]))  # days 5-8 are indices 4-7
    
    # Athens between day 8 and 11
    s.add(Or([day_to_city[i] == city_to_int["Athens"] for i in range(7, 11)]))  # days 8-11 are indices 7-10
    
    # Mykonos on day 27 and 28
    s.add(day_to_city[26] == city_to_int["Mykonos"])  # day 27 is index 26
    s.add(day_to_city[27] == city_to_int["Mykonos"])  # day 28 is index 27
    
    # Flight constraints: consecutive days must be either the same city or have a direct flight
    for i in range(27):
        current_day = day_to_city[i]
        next_day = day_to_city[i+1]
        same_city = current_day == next_day
        can_fly = Or([And(current_day == city_to_int[city1], next_day == city_to_int[city2]) 
                     for city1 in cities 
                     for city2 in direct_flights.get(city1, [])])
        s.add(Or(same_city, can_fly))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(28):
            city_idx = model.evaluate(day_to_city[i]).as_long()
            itinerary.append({"day": i+1, "place": int_to_city[city_idx]})
        
        # Verify all constraints are met
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry["place"]] += 1
        
        for city in cities:
            assert city_days[city] == durations[city], f"Duration mismatch for {city}"
        
        # Verify time windows
        copenhagen_days = [entry["day"] for entry in itinerary if entry["place"] == "Copenhagen"]
        assert any(11 <= day <= 15 for day in copenhagen_days), "Copenhagen window not met"
        
        naples_days = [entry["day"] for entry in itinerary if entry["place"] == "Naples"]
        assert any(5 <= day <= 8 for day in naples_days), "Naples window not met"
        
        athens_days = [entry["day"] for entry in itinerary if entry["place"] == "Athens"]
        assert any(8 <= day <= 11 for day in athens_days), "Athens window not met"
        
        mykonos_days = [entry["day"] for entry in itinerary if entry["place"] == "Mykonos"]
        assert 27 in mykonos_days and 28 in mykonos_days, "Mykonos conference days not met"
        
        # Verify flight constraints
        for i in range(27):
            current_city = itinerary[i]["place"]
            next_city = itinerary[i+1]["place"]
            if current_city != next_city:
                assert next_city in direct_flights[current_city], f"No direct flight from {current_city} to {next_city} on day {i+1}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the function and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))