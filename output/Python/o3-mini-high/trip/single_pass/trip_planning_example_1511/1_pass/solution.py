#!/usr/bin/env python3
import json

# Define fixed durations for each city
durations = {
    "Venice": 3,
    "Reykjavik": 2,
    "Munich": 3,
    "Santorini": 3,
    "Manchester": 3,
    "Porto": 3,
    "Bucharest": 5,
    "Tallinn": 4,
    "Valencia": 2,
    "Vienna": 5
}

# For the three cities with fixed event timing we require:
# Munich must include days 4–6  => its visit must start on day 4.
# Santorini must include days 8–10 => its visit must start on day 8.
# Valencia must include days 14–15 => its visit must start on day 14.
event_start = {
    "Munich": 4,
    "Santorini": 8,
    "Valencia": 14
}

# Define the graph of direct flights (bidirectional; each edge appears for both cities)
flight_graph = {
    "Bucharest": {"Manchester", "Valencia", "Vienna", "Munich", "Santorini"},
    "Manchester": {"Bucharest", "Santorini", "Vienna", "Venice", "Munich", "Porto"},
    "Munich": {"Venice", "Porto", "Manchester", "Reykjavik", "Vienna", "Bucharest", "Valencia", "Tallinn"},
    "Venice": {"Munich", "Santorini", "Manchester", "Vienna"},
    "Reykjavik": {"Vienna", "Munich"},
    "Santorini": {"Manchester", "Venice", "Vienna", "Bucharest"},
    "Porto": {"Munich", "Vienna", "Manchester", "Valencia"},
    "Tallinn": {"Munich"},
    "Valencia": {"Vienna", "Bucharest", "Porto", "Munich"},
    "Vienna": {"Reykjavik", "Manchester", "Porto", "Santorini", "Venice", "Bucharest", "Munich", "Valencia"}
}

# List of all cities
all_cities = list(durations.keys())

# Global solution container (a valid ordering of all cities)
solution = None

# Backtracking search:
# order: a list of cities selected so far.
# used: a set of cities already in the order.
# cumulative: the sum of durations for the cities in 'order'
# The computed start day for the city to be added at index i is: 1 + (sum of durations of previous cities) - (i)
def backtrack(order, used, cumulative):
    global solution
    if solution is not None:
        return

    # When a full ordering is achieved (10 cities),
    # the overall trip goes from Day 1 to Day (1 + total_duration - total_flights)
    if len(order) == len(all_cities):
        solution = order.copy()
        return

    # For deterministic results, iterate over remaining cities sorted alphabetically.
    for city in sorted(set(all_cities) - used):
        # Flight connectivity check: if there is at least one city already, then
        # the next flight must be a direct connection from the last city.
        if order:
            last_city = order[-1]
            if city not in flight_graph[last_city]:
                continue

        # Compute the planned start day for the candidate city.
        # For a city placed at position i (0-indexed), the start day is:
        #   start_day = 1 + (sum of durations of cities before it) - (i)
        index = len(order)
        candidate_start = 1 + cumulative - index

        # If this city has an event constraint then its start day must equal the required day.
        if city in event_start:
            if candidate_start != event_start[city]:
                continue

        # Accept the candidate and advance.
        new_order = order + [city]
        new_used = used | {city}
        new_cumulative = cumulative + durations[city]
        backtrack(new_order, new_used, new_cumulative)
        if solution is not None:
            return

# Start backtracking with an empty order.
backtrack([], set(), 0)

# Once a valid ordering is found, compute the itinerary day ranges.
# If one flies from A to B on day X, then day X counts for both A and B.
# In our computed segmentation, the visit for city i:
#    start_day = 1 + (sum of durations for cities before i) - (i)
#    end_day = start_day + durations[city] - 1
itinerary = []
if solution:
    current_cumulative = 0
    for i, city in enumerate(solution):
        start_day = 1 + current_cumulative - i
        end_day = start_day + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        current_cumulative += durations[city]

result = {"itinerary": itinerary}
print(json.dumps(result))