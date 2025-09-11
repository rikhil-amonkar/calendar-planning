import json

# Define the cities and their required durations
cities = {
    "Oslo": 2,
    "Dubrovnik": 3,
    "Helsinki": 2,
    "Krakow": 5,
    "Vilnius": 2,
    "Paris": 2,
    "Madrid": 5,
    "Mykonos": 4
}

# Define direct flights between cities
direct_flights = {
    "Oslo": ["Krakow", "Paris", "Madrid", "Helsinki", "Vilnius", "Dubrovnik"],
    "Krakow": ["Oslo", "Paris", "Vilnius", "Helsinki", "Madrid"],
    "Paris": ["Oslo", "Krakow", "Madrid", "Helsinki", "Vilnius"],
    "Helsinki": ["Oslo", "Krakow", "Paris", "Dubrovnik", "Madrid"],
    "Vilnius": ["Oslo", "Krakow", "Paris"],
    "Dubrovnik": ["Helsinki", "Madrid", "Oslo"],
    "Madrid": ["Paris", "Dubrovnik", "Helsinki", "Oslo", "Mykonos"],
    "Mykonos": ["Madrid"]
}

# Define the required constraints for specific cities
constraints = {
    "Oslo": {"start_day": 1, "end_day": 2},
    "Dubrovnik": {"start_day": 2, "end_day": 4},
    "Mykonos": {"start_day": 15, "end_day": 18}
}

# Define the order of cities based on constraints and direct flights
itinerary_order = ["Oslo", "Dubrovnik", "Helsinki", "Krakow", "Vilnius", "Paris", "Madrid", "Mykonos"]

# Calculate day ranges for each city in the itinerary
itinerary = []
current_day = 1

for city in itinerary_order:
    duration = cities[city]
    start_day = current_day
    end_day = start_day + duration - 1
    if city in constraints:
        # Enforce specific day ranges for constrained cities
        start_day = constraints[city]["start_day"]
        end_day = constraints[city]["end_day"]
    else:
        # Calculate based on previous city
        pass
    itinerary.append({
        "day_range": f"Day {start_day}-{end_day}",
        "place": city
    })
    current_day = end_day + 1

# Output the result as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))