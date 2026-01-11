import json

# Define the constraints
constraints = {
    "Venice": {"days": 3},
    "Reykjavik": {"days": 2},
    "Munich": {"days": 3, "event_days": range(4, 7)},  # Days 4 to 6
    "Santorini": {"days": 3, "visit_days": range(8, 11)},  # Days 8 to 10
    "Manchester": {"days": 3},
    "Porto": {"days": 3},
    "Bucharest": {"days": 5},
    "Tallinn": {"days": 4},
    "Valencia": {"days": 2, "workshop_days": range(14, 16)},  # Days 14 and 15
    "Vienna": {"days": 5}
}

# Define the flight network as a dictionary of sets
flight_network = {
    "Bucharest": {"Manchester", "Valencia", "Vienna"},
    "Munich": {"Venice", "Porto", "Manchester", "Reykjavik", "Vienna", "Bucharest", "Tallinn", "Santorini", "Valencia"},
    "Santorini": {"Venice", "Manchester", "Vienna", "Bucharest"},
    "Vienna": {"Reykjavik", "Venice", "Santorini", "Manchester", "Porto", "Valencia", "Bucharest"},
    "Venice": {"Munich", "Santorini", "Manchester", "Vienna"},
    "Reykjavik": {"Vienna", "Munich"},
    "Manchester": {"Santorini", "Vienna", "Porto", "Munich", "Venice", "Bucharest"},
    "Porto": {"Vienna", "Manchester", "Valencia", "Munich"},
    "Valencia": {"Vienna", "Manchester", "Porto", "Bucharest", "Munich"},
    "Tallinn": {"Munich"}
}

# Initialize the itinerary
itinerary = []
current_day = 1
visited_cities = set()

def find_next_city(current_city, visited_cities):
    for city in flight_network[current_city]:
        if city not in visited_cities:
            return city
    return None

# Place mandatory stays
for city, details in constraints.items():
    if "event_days" in details or "visit_days" in details or "workshop_days" in details:
        days = max(details.get("event_days", []), details.get("visit_days", []), details.get("workshop_days", []))
        start_day = days.start
        end_day = days.stop - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        current_day = end_day + 1
        visited_cities.add(city)

# Fill in the rest of the days
while current_day <= 24:
    for city, details in constraints.items():
        if city not in visited_cities and current_day + details["days"] - 1 <= 24:
            end_day = current_day + details["days"] - 1
            itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": city})
            current_day = end_day + 1
            visited_cities.add(city)
            break
    else:
        # If no city can be added directly, find a transition city
        last_city = itinerary[-1]["place"]
        next_city = find_next_city(last_city, visited_cities)
        if next_city:
            # Add a single day in the next city to facilitate transition
            itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": next_city})
            current_day += 1
            visited_cities.add(next_city)

# Output the itinerary as JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=4))