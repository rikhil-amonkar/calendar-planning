#!/usr/bin/env python3
import json

# Define the cities and their fixed durations and special constraints.
durations = {
    "Prague": 5,
    "Tallinn": 3,
    "Warsaw": 2,
    "Porto": 3,
    "Naples": 5,
    "Milan": 3,
    "Lisbon": 5,
    "Santorini": 5,
    "Riga": 4,
    "Stockholm": 2
}

cities = list(durations.keys())

# Build the flight graph.
# Most flights are bidirectional except two that are one-way:
#   - Stockholm -> Santorini (only from Stockholm to Santorini)
#   - Riga -> Tallinn (only from Riga to Tallinn)
flight_edges = [
    ("Riga", "Prague"),
    ("Stockholm", "Milan"),
    ("Riga", "Milan"),
    ("Lisbon", "Stockholm"),
    ("Naples", "Warsaw"),
    ("Lisbon", "Warsaw"),
    ("Naples", "Milan"),
    ("Lisbon", "Naples"),
    ("Tallinn", "Prague"),
    ("Stockholm", "Warsaw"),
    ("Riga", "Warsaw"),
    ("Lisbon", "Riga"),
    ("Riga", "Stockholm"),
    ("Lisbon", "Porto"),
    ("Lisbon", "Prague"),
    ("Milan", "Porto"),
    ("Prague", "Milan"),
    ("Lisbon", "Milan"),
    ("Warsaw", "Porto"),
    ("Warsaw", "Tallinn"),
    ("Santorini", "Milan"),
    ("Stockholm", "Prague"),
    ("Stockholm", "Tallinn"),
    ("Warsaw", "Milan"),
    ("Santorini", "Naples"),
    ("Warsaw", "Prague")
]

# Create dictionary for flights.
flights = {city: set() for city in cities}

# Add bidirectional edges.
for c1, c2 in flight_edges:
    flights[c1].add(c2)
    flights[c2].add(c1)

# Now add the one-way directed flights.
# Stockholm -> Santorini (only add Santorini to Stockholm's neighbor, not vice-versa)
flights["Stockholm"].add("Santorini")
# Riga -> Tallinn (only add Tallinn to Riga's neighbor)
flights["Riga"].add("Tallinn")
# Note: In the bidirectional additions above, some pairs might already exist.
# For the directed flights, we do not add the reverse direction.

# Special constraint check function.
def meets_constraint(city, start_day):
    # For Riga, we must catch the annual show from Day 5 to Day 8.
    # With a 4-day stay, that forces the visit to be exactly from Day 5 to Day 8.
    if city == "Riga":
        return start_day == 5
    # For Tallinn, must visit relatives between Day 18 and 20.
    # With a 3-day stay (block = start_day to start_day+2), we require that
    # the block overlaps [18,20].  This means start_day <= 20 and start_day+2 >= 18.
    if city == "Tallinn":
        return (start_day <= 20) and (start_day + durations[city] - 1 >= 18) and (start_day >= 16)
    # For Milan, must meet friend between Day 24 and 26.
    # With a 3-day stay, block = start_day to start_day+2.
    # It must overlap [24,26] so start_day <= 26 and start_day+2 >= 24.
    if city == "Milan":
        return (start_day <= 26) and (start_day + durations[city] - 1 >= 24) and (start_day >= 22)
    return True

# The start-day for the 0th city is always day 1.
# For a city placed in slot i (0-indexed), its start day is:
#    1 + sum_{j=0}^{i-1} (durations[city_j] - 1)
def compute_start_day(order):
    day = 1
    for city in order[:-1]:
        day += durations[city] - 1
    return day

# We'll use DFS/backtracking to find a valid ordering.
def dfs(order, used, current_day):
    if len(order) == len(cities):
        # When all cities are scheduled, the trip automatically ends on Day 28.
        return order
    
    for city in cities:
        if city in used:
            continue
        # If there is a previous city, check if a direct flight exists.
        if order:
            last_city = order[-1]
            if city not in flights[last_city]:
                continue
        # Check if the city's special constraint is met given the current start day.
        if not meets_constraint(city, current_day):
            continue

        # Choose this city.
        new_order = order + [city]
        new_used = used | {city}
        # The new starting day for the next city is current_day + (duration - 1)
        next_day = current_day + (durations[city] - 1)
        result = dfs(new_order, new_used, next_day)
        if result is not None:
            return result
    return None

def build_itinerary(order):
    itinerary = []
    day = 1
    for city in order:
        start = day
        end = day + durations[city] - 1
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
        # For the next city, the flight day is shared: new start day = current start + (duration - 1)
        day += durations[city] - 1
    return itinerary

def main():
    # Start the DFS with an empty order; the first city will have start_day=1.
    solution = dfs([], set(), 1)
    if solution is None:
        result = {"itinerary": []}
    else:
        itinerary = build_itinerary(solution)
        result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()