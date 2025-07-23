from z3 import *
import json

def solve_itinerary():
    # Cities to visit
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
    
    # Direct flights as a dictionary for quick lookup
    direct_flights = {
        "Copenhagen": ["Dubrovnik", "Brussels", "Prague", "Naples", "Munich", "Athens", "Geneva", "Santorini"],
        "Brussels": ["Copenhagen", "Naples", "Prague", "Athens", "Munich", "Geneva"],
        "Prague": ["Geneva", "Athens", "Copenhagen", "Brussels", "Munich"],
        "Geneva": ["Prague", "Athens", "Mykonos", "Santorini", "Naples", "Dubrovnik", "Munich", "Brussels", "Copenhagen"],
        "Athens": ["Geneva", "Dubrovnik", "Mykonos", "Naples", "Prague", "Santorini", "Brussels", "Munich", "Copenhagen"],
        "Dubrovnik": ["Copenhagen", "Naples", "Athens", "Geneva", "Munich"],
        "Naples": ["Dubrovnik", "Mykonos", "Copenhagen", "Athens", "Munich", "Geneva", "Santorini", "Brussels"],
        "Mykonos": ["Geneva", "Naples", "Athens", "Munich"],
        "Santorini": ["Geneva", "Athens", "Naples", "Copenhagen"],
        "Munich": ["Mykonos", "Dubrovnik", "Brussels", "Athens", "Geneva", "Copenhagen", "Prague", "Naples"]
    }
    
    # Create a Z3 solver instance with a timeout
    s = Solver()
    s.set("timeout", 60000)  # Set timeout to 60 seconds
    
    # Create variables for each day: day 1 to day 28. Each day is represented by an integer corresponding to the city's index in the 'cities' list.
    days = [Int(f"day_{i}") for i in range(1, 29)]
    
    # Each day variable must be between 0 and 9 (inclusive), representing the 10 cities.
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Add constraints for city durations.
    # The total number of days spent in each city must meet the specified durations.
    city_durations = {
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
    
    for city_idx, city in enumerate(cities):
        duration = city_durations[city]
        # The count of days where the city is present.
        s.add(Sum([If(day == city_idx, 1, 0) for day in days]) == duration)
    
    # Add constraints for specific city visits in certain day ranges.
    # Copenhagen must be visited between day 11 and day 15 (at least one day in this range).
    s.add(Or([days[i] == cities.index("Copenhagen") for i in range(10, 15)]))  # days 11-15 (0-based indices 10-14)
    
    # Conference in Mykonos on day 27 and 28.
    s.add(days[26] == cities.index("Mykonos"))  # day 27 is index 26
    s.add(days[27] == cities.index("Mykonos"))  # day 28 is index 27
    
    # Relatives in Naples between day 5 and day 8 (at least one day in this range).
    s.add(Or([days[i] == cities.index("Naples") for i in range(4, 8)]))  # days 5-8 (indices 4-7)
    
    # Workshop in Athens between day 8 and day 11.
    s.add(Or([days[i] == cities.index("Athens") for i in range(7, 11)]))  # days 8-11 (indices 7-10)
    
    # Flight constraints: consecutive days must be either the same city or have a direct flight.
    for i in range(len(days) - 1):
        current_city = days[i]
        next_city = days[i + 1]
        # The next city must be either the same as current or a directly connected city.
        same_city = (current_city == next_city)
        # Create a condition for each possible current city and check if the next city is connected
        flight_conditions = []
        for current_city_idx in range(len(cities)):
            current_city_name = cities[current_city_idx]
            connected_cities = direct_flights.get(current_city_name, [])
            for next_city_idx in range(len(cities)):
                next_city_name = cities[next_city_idx]
                if next_city_name in connected_cities:
                    flight_conditions.append(And(current_city == current_city_idx, next_city == next_city_idx))
        s.add(Or(same_city, Or(flight_conditions)))
    
    # Check if the solver can find a solution.
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(len(days)):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = cities[city_idx]
            itinerary.append({"day": day_num, "place": city})
        
        # Verify that the itinerary meets all constraints.
        # For example, check city durations.
        city_day_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_day_counts[entry["place"]] += 1
        
        for city in city_day_counts:
            assert city_day_counts[city] == city_durations[city], f"Duration mismatch for {city}"
        
        # Check specific day constraints.
        copenhagen_days = [entry["day"] for entry in itinerary if entry["place"] == "Copenhagen"]
        assert any(11 <= day <= 15 for day in copenhagen_days), "Copenhagen visit not between days 11-15"
        
        assert itinerary[26]["place"] == "Mykonos" and itinerary[27]["place"] == "Mykonos", "Mykonos conference days incorrect"
        
        naples_days = [entry["day"] for entry in itinerary if entry["place"] == "Naples"]
        assert any(5 <= day <= 8 for day in naples_days), "Naples relatives visit not between days 5-8"
        
        athens_days = [entry["day"] for entry in itinerary if entry["place"] == "Athens"]
        assert any(8 <= day <= 11 for day in athens_days), "Athens workshop not between days 8-11"
        
        # Check flight connections.
        for i in range(len(itinerary) - 1):
            current_place = itinerary[i]["place"]
            next_place = itinerary[i + 1]["place"]
            if current_place != next_place:
                assert next_place in direct_flights.get(current_place, []), f"No direct flight from {current_place} to {next_place} on day {i + 1}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the function and print the result in JSON format.
result = solve_itinerary()
print(json.dumps(result, indent=2))