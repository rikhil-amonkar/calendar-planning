#!/usr/bin/env python3
import itertools
import json

def main():
    # Total trip length in unique days
    total_days = 20

    # Required days per city (note that the duration numbers include the flight overlap days)
    city_durations = {
        "Nice": 5,       # Must be visited from day 1-5 (relatives)
        "Krakow": 6,     # 6 days in Krakow
        "Dublin": 7,     # 7 days in Dublin
        "Lyon": 4,       # 4 days in Lyon
        "Frankfurt": 2   # 2 days in Frankfurt - meeting friends between day 19 and day 20
    }

    # List of available direct flights (undirected)
    flight_edges = [
        ("Nice", "Dublin"),
        ("Dublin", "Frankfurt"),
        ("Dublin", "Krakow"),
        ("Krakow", "Frankfurt"),
        ("Lyon", "Frankfurt"),
        ("Nice", "Frankfurt"),
        ("Lyon", "Dublin"),
        ("Nice", "Lyon")
    ]

    # Build bidirectional flight graph.
    graph = {city: set() for city in city_durations.keys()}
    for c1, c2 in flight_edges:
        graph[c1].add(c2)
        graph[c2].add(c1)

    # Fixed start and end to meet the special constraints:
    # - "Nice" (with relatives) must be at the start (Day 1-5)
    # - "Frankfurt" (meeting friends) must be at the end (covers days 19-20)
    start_city = "Nice"
    end_city = "Frankfurt"
    middle_cities = [city for city in city_durations if city not in [start_city, end_city]]

    # Generate valid orderings that respect direct flight connections.
    valid_orderings = []
    for perm in itertools.permutations(middle_cities):
        itinerary_order = [start_city] + list(perm) + [end_city]
        valid = True
        for i in range(len(itinerary_order) - 1):
            current = itinerary_order[i]
            next_city = itinerary_order[i + 1]
            if next_city not in graph[current]:
                valid = False
                break
        if valid:
            valid_orderings.append(itinerary_order)

    # For a given ordering, compute the schedule as day ranges.
    # NOTE: When flying between cities, the flight day counts for both cities.
    def compute_schedule(order):
        itinerary_schedule = []
        current_day = 1
        for city in order:
            duration = city_durations[city]
            start = current_day
            end = start + duration - 1  # The departure/arrival day is double-counted.
            itinerary_schedule.append({"day_range": "Day {}-{}".format(start, end), "place": city})
            # Next city starts on the same day that the current city ends.
            current_day = end
        # Return the itinerary and the actual last day reached.
        return itinerary_schedule, current_day

    # Find an ordering whose schedule exactly covers the planned total_days.
    optimal_schedule = None
    for order in valid_orderings:
        schedule, last_day = compute_schedule(order)
        if last_day == total_days:
            # Verify that Nice is Day 1-5 and Frankfurt is Day 19-20.
            if schedule[0]["day_range"] == "Day 1-5" and schedule[-1]["day_range"] == "Day 19-20":
                optimal_schedule = schedule
                break

    if optimal_schedule is None:
        output = {"itinerary": [{"error": "No valid itinerary found."}]}
    else:
        output = {"itinerary": optimal_schedule}

    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()

You can run this code without encountering the nonprintable character error.