#!/usr/bin/env python3
import json

# Total days and required durations for each city.
total_days = 25
durations = {
    "Paris": 2,
    "Barcelona": 5,
    "Florence": 5,
    "Amsterdam": 2,
    "Tallinn": 2,
    "Vilnius": 3,
    "Warsaw": 4,
    "Venice": 3,
    "Hamburg": 4,
    "Salzburg": 4
}

# Event time-window constraints.
# They are checked on the computed start day for that city.
def meets_constraint(city, start):
    # The city's stay is from start to start + duration - 1.
    end = start + durations[city] - 1
    if city == "Paris":
        # Workshop in Paris between day 1 and 2. Must be present on day 1 or 2.
        # If Paris's stay is [start, end], require that it overlaps [1,2].
        if not (start <= 2 and end >= 1):
            return False
    if city == "Barcelona":
        # Meet friends in Barcelona between day 2 and day 6.
        # We require that the Barcelona period [start, start+4] intersects [2,6].
        if not (start <= 6 and end >= 2):
            return False
    if city == "Tallinn":
        # Meet friend in Tallinn between day 11 and day 12.
        # For a 2-day stay [start, start+1], we require an overlap with [11,12].
        # That forces start to be between 10 and 12 (inclusive) so that day 11 or 12 is covered.
        if not (10 <= start <= 12):
            return False
    if city == "Hamburg":
        # Conference in Hamburg during day 19 through 22.
        # For a 4-day stay [start, start+3] to cover days 19-22, start must be exactly 19.
        if start != 19:
            return False
    if city == "Salzburg":
        # Wedding in Salzburg between day 22 and 25.
        # For a 4-day stay [start, start+3] to cover days 22-25, start must be exactly 22.
        if start != 22:
            return False
    return True

# Define the flight network.
# Most flights are bidirectional (symmetric) except for the special case "from Tallinn to Vilnius".
all_cities = ["Paris", "Barcelona", "Florence", "Amsterdam", "Tallinn", "Vilnius", "Warsaw", "Venice", "Hamburg", "Salzburg"]

# List of symmetric flight connections.
symmetric_pairs = [
    ("Paris", "Venice"),
    ("Barcelona", "Amsterdam"),
    ("Amsterdam", "Warsaw"),
    ("Amsterdam", "Vilnius"),
    ("Barcelona", "Warsaw"),
    ("Warsaw", "Venice"),
    ("Amsterdam", "Hamburg"),
    ("Barcelona", "Hamburg"),
    ("Barcelona", "Florence"),
    ("Barcelona", "Venice"),
    ("Paris", "Hamburg"),
    ("Paris", "Vilnius"),
    ("Paris", "Amsterdam"),
    ("Paris", "Florence"),
    ("Florence", "Amsterdam"),
    ("Vilnius", "Warsaw"),
    ("Barcelona", "Tallinn"),
    ("Paris", "Warsaw"),
    ("Tallinn", "Warsaw"),
    ("Amsterdam", "Tallinn"),
    ("Paris", "Tallinn"),
    ("Paris", "Barcelona"),
    ("Venice", "Hamburg"),
    ("Warsaw", "Hamburg"),
    ("Hamburg", "Salzburg"),
    ("Amsterdam", "Venice")
]

# List of directional flight connections.
directional_pairs = [
    ("Tallinn", "Vilnius")  # Only from Tallinn to Vilnius.
]

# Build flight graph as a dictionary: city -> set(neighboring cities)
flight_graph = {city: set() for city in all_cities}
for a, b in symmetric_pairs:
    flight_graph[a].add(b)
    flight_graph[b].add(a)
for a, b in directional_pairs:
    flight_graph[a].add(b)
    # Do not add the reverse direction.

# Backtracking search for a valid itinerary.
# The schedule is a list of tuples: (city, start_day, end_day)
# The rule: for the first city, start=1, end = start+duration-1.
# For each subsequent city, start = previous city's end_day (overlap due to flight) 
# and end = start + duration - 1.
def search_itinerary(path, schedule, remaining):
    if not remaining:
        # When complete, the final city should end at total_days.
        # With our arithmetic, total end will be sum(durations) - (len(path)-1).
        if schedule[-1][2] == total_days:
            return schedule
        else:
            return None
    last_city = path[-1]
    last_end = schedule[-1][2]
    for candidate in sorted(remaining):
        # Check direct flight connectivity.
        if candidate not in flight_graph[last_city]:
            continue
        # Compute the candidate's start and end days.
        new_start = last_end  # flight day overlap: on the flight day, you're in both cities.
        new_end = new_start + durations[candidate] - 1
        
        # Check the candidate's event constraints.
        if not meets_constraint(candidate, new_start):
            continue
        
        # Tentatively add candidate to itinerary.
        new_schedule = schedule + [(candidate, new_start, new_end)]
        new_path = path + [candidate]
        new_remaining = remaining - {candidate}
        result = search_itinerary(new_path, new_schedule, new_remaining)
        if result is not None:
            return result
    return None

def main():
    # We force Paris to be the starting city to meet its workshop constraint.
    starting_city = "Paris"
    initial_schedule = [(starting_city, 1, 1 + durations[starting_city] - 1)]  # (Paris, 1, 2)
    remaining = set(all_cities) - {starting_city}
    itinerary_schedule = search_itinerary([starting_city], initial_schedule, remaining)
    if not itinerary_schedule:
        result = {"itinerary": []}
    else:
        # Format the itinerary as a list of dictionaries with day_range and place.
        itinerary_list = []
        for city, start, end in itinerary_schedule:
            itinerary_list.append({
                "day_range": "Day {}-{}".format(start, end),
                "place": city
            })
        result = {"itinerary": itinerary_list}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()