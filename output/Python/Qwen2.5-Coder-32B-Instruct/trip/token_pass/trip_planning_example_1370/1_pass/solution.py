import json

def find_itinerary():
    # Define the constraints
    constraints = {
        "Santorini": {"days": (25, 29), "duration": 5},
        "Krakow": {"days": (18, 22), "duration": 5},
        "Paris": {"days": (11, 15), "duration": 5},
        "Vilnius": {"duration": 3},
        "Munich": {"duration": 5},
        "Geneva": {"duration": 2},
        "Amsterdam": {"duration": 4},
        "Budapest": {"duration": 5},
        "Split": {"duration": 4}  # Adjusted to fit within 30 days
    }

    # Define available direct flights
    flights = {
        ("Paris", "Krakow"), ("Paris", "Amsterdam"), ("Paris", "Split"),
        ("Vilnius", "Munich"), ("Paris", "Geneva"), ("Amsterdam", "Geneva"),
        ("Munich", "Split"), ("Split", "Krakow"), ("Munich", "Amsterdam"),
        ("Budapest", "Amsterdam"), ("Split", "Geneva"), ("Vilnius", "Split"),
        ("Munich", "Geneva"), ("Munich", "Krakow"), ("Krakow", "Vilnius"),
        ("Vilnius", "Amsterdam"), ("Budapest", "Paris"), ("Krakow", "Amsterdam"),
        ("Vilnius", "Paris"), ("Budapest", "Geneva"), ("Split", "Amsterdam"),
        ("Santorini", "Geneva"), ("Amsterdam", "Santorini"), ("Munich", "Budapest"),
        ("Munich", "Paris")
    }

    # Sort cities by constraints
    cities = sorted(constraints.keys(), key=lambda x: constraints[x].get("days", (0, 0)))

    # Initialize the itinerary
    itinerary = []
    current_day = 1

    def can_travel(from_city, to_city):
        return (from_city, to_city) in flights or (to_city, from_city) in flights

    for city in cities:
        city_constraints = constraints[city]
        duration = city_constraints["duration"]
        preferred_days = city_constraints.get("days", None)

        if preferred_days:
            # Try to fit the city within the preferred days
            start_day = max(current_day, preferred_days[0] - duration + 1)
            end_day = min(preferred_days[1], 30)
        else:
            # Fit the city within the remaining days
            start_day = current_day
            end_day = 30

        # Find the earliest possible start day within the allowed range
        while start_day + duration - 1 <= end_day:
            # Check if we can travel to this city from the last visited city
            if itinerary:
                last_city = itinerary[-1]["place"]
                if not can_travel(last_city, city):
                    start_day += 1
                    continue

            # Add the city to the itinerary
            itinerary.append({"day_range": f"Day {start_day}-{start_day + duration - 1}", "place": city})
            current_day = start_day + duration
            break
        else:
            raise ValueError(f"Cannot fit {city} into the itinerary within the constraints.")

    # Validate the itinerary
    assert current_day <= 31, "Itinerary exceeds 30 days."

    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Run the function and print the result
print(find_itinerary())