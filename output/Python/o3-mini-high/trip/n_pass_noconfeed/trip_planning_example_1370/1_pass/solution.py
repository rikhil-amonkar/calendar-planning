import itertools
import json

def main():
    # Define each city's duration
    durations = {
        "Santorini": 5,
        "Krakow": 5,
        "Paris": 5,
        "Vilnius": 3,
        "Munich": 5,
        "Geneva": 2,
        "Amsterdam": 4,
        "Budapest": 5,
        "Split": 4,
    }

    # Define meeting/wedding constraints as (min_start, max_start) for the 5‐day block
    meeting_constraints = {
        "Paris": (7, 15),      # Must have at least one day in [11,15]
        "Krakow": (14, 22),    # Wedding between day 18 and day 22
        "Santorini": (21, 29), # Meeting with friends between day 25 and day 29
    }

    # List of flight routes (a, b, bidirectional)
    # For directional ones, bidirectional is False.
    flights = [
        ("Paris", "Krakow", True),
        ("Paris", "Amsterdam", True),
        ("Paris", "Split", True),
        ("Vilnius", "Munich", False),    # only from Vilnius to Munich
        ("Paris", "Geneva", True),
        ("Amsterdam", "Geneva", True),
        ("Munich", "Split", True),
        ("Split", "Krakow", True),
        ("Munich", "Amsterdam", True),
        ("Budapest", "Amsterdam", True),
        ("Split", "Geneva", True),
        ("Vilnius", "Split", True),
        ("Munich", "Geneva", True),
        ("Munich", "Krakow", True),
        ("Krakow", "Vilnius", False),     # only from Krakow to Vilnius
        ("Vilnius", "Amsterdam", True),
        ("Budapest", "Paris", True),
        ("Krakow", "Amsterdam", True),
        ("Vilnius", "Paris", True),
        ("Budapest", "Geneva", True),
        ("Split", "Amsterdam", True),
        ("Santorini", "Geneva", True),
        ("Amsterdam", "Santorini", True),
        ("Munich", "Budapest", True),
        ("Munich", "Paris", True)
    ]

    # Build the flight graph as an adjacency list (directional where required)
    cities = list(durations.keys())
    graph = {city: set() for city in cities}
    for a, b, bidir in flights:
        graph[a].add(b)
        if bidir:
            graph[b].add(a)

    # Given an itinerary permutation, compute the schedule and check constraints.
    # The schedule is computed as follows:
    #   S[0] = 1
    #   For i > 0, S[i] = S[i-1] + durations[perm[i-1]] - 1.
    # Also check that if a city has a meeting constraint, its start day S[i] lies within the allowed window.
    # And check that there is a valid direct flight from each city to the next in the permutation.
    def check_itinerary(perm):
        current_day = 1
        # For each city in the permutation, in order.
        for i, city in enumerate(perm):
            # If the city has an event constraint, ensure the 5-day block starting today intersects the required window.
            if city in meeting_constraints:
                min_start, max_start = meeting_constraints[city]
                if current_day < min_start or current_day > max_start:
                    return None
            # For every transition (except the last city), check for a valid direct flight.
            if i < len(perm) - 1:
                next_city = perm[i+1]
                if next_city not in graph[city]:
                    return None
            # Update current_day for the next city.
            current_day = current_day + durations[city] - 1
        # If all constraints are met, compute and return the full schedule.
        return compute_schedule(perm)

    # Compute the schedule list: each element is (start_day, end_day, city)
    def compute_schedule(perm):
        schedule = []
        current_day = 1
        for city in perm:
            start_day = current_day
            end_day = current_day + durations[city] - 1
            schedule.append((start_day, end_day, city))
            current_day = current_day + durations[city] - 1
        return schedule

    valid_schedule = None
    # Iterate through all permutations of the 9 cities
    for perm in itertools.permutations(cities):
        # Skip itineraries that start with a city that has a timing constraint 
        # because S would be 1 (which wouldn't satisfy the min start day condition)
        if perm[0] in meeting_constraints:
            continue
        schedule = check_itinerary(perm)
        if schedule is not None:
            valid_schedule = schedule
            break

    if valid_schedule is None:
        result = {"itinerary": []}
    else:
        itinerary = []
        for start_day, end_day, city in valid_schedule:
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        result = {"itinerary": itinerary}

    print(json.dumps(result))

if __name__ == "__main__":
    main()