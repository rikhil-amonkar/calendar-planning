#!/usr/bin/env python3
import json

# Define the cities and their minimum stay durations (in days)
durations = {
    "Geneva": 4,
    "Istanbul": 4,
    "Venice": 5,
    "Madrid": 4,
    "Munich": 5,
    "Reykjavik": 2,
    "Vienna": 4,
    "Riga": 2,
    "Vilnius": 4,
    "Brussels": 2
}

# Special time window constraints (inclusive) for events in certain cities.
# Each value is a tuple (window_start, window_end)
special_windows = {
    "Geneva": (1, 4),      # visit relatives in Geneva between day 1 and day 4
    "Venice": (7, 11),     # attend a workshop in Venice between day 7 and day 11
    "Vilnius": (20, 23),   # meet friends in Vilnius between day 20 and day 23
    "Brussels": (26, 27)   # attend a wedding in Brussels between day 26 and day 27
}

# Define the flight network (bidirectional edges)
flight_graph = {
    "Geneva": {"Istanbul", "Vienna", "Brussels", "Madrid", "Munich"},
    "Istanbul": {"Geneva", "Brussels", "Venice", "Vienna", "Riga", "Munich", "Madrid", "Vilnius"},
    "Venice": {"Brussels", "Munich", "Vienna", "Istanbul", "Madrid"},
    "Madrid": {"Munich", "Venice", "Vienna", "Brussels", "Istanbul", "Reykjavik", "Geneva"},
    "Munich": {"Vienna", "Reykjavik", "Istanbul", "Madrid", "Brussels", "Riga", "Vilnius", "Geneva", "Venice"},
    "Reykjavik": {"Munich", "Vienna", "Madrid", "Brussels"},
    "Vienna": {"Munich", "Vilnius", "Istanbul", "Venice", "Riga", "Brussels", "Geneva", "Madrid"},
    "Riga": {"Brussels", "Istanbul", "Munich", "Vilnius"},
    "Vilnius": {"Vienna", "Istanbul", "Brussels", "Munich", "Riga"},
    "Brussels": {"Istanbul", "Venice", "Riga", "Reykjavik", "Vilnius", "Madrid", "Vienna", "Geneva", "Munich"}
}

# Total trip days (including overlapping flight days)
TOTAL_DAYS = 27

# Pre-calculate the sum of durations of all cities for feasibility (should equal 36)
total_duration = sum(durations[city] for city in durations)
# The itinerary total with flight-day overlap is: first city contributes full duration
# and each subsequent city contributes (duration - 1)
# So total trip days = durations[first] + sum(duration - 1 for each other city)
# For any ordering, this equals (sum of durations) - (number of cities - 1)
# For our data: 36 - (10 - 1) = 36 - 9 = 27, which matches TOTAL_DAYS.

# Function to check if an interval [start, end] (both inclusive) intersects with a window [w_start, w_end]
def interval_intersects(start, end, w_start, w_end):
    return not (end < w_start or start > w_end)

# For a given set of remaining cities, the minimal additional days required (assuming best-case ordering)
# When ordering remaining cities, the first one adds full duration and each subsequent adds (duration - 1)
def min_additional_days(remaining):
    if not remaining:
        return 0
    # Because order does not really affect the sum: it will be:
    # min_days = min_{city in remaining} { durations[city] + sum(durations[r] for r in remaining - {city}) - (len(remaining)-1) }
    # But note that for any ordering the sum becomes: (sum(durations) - (number of remaining - 1))
    return sum(durations[city] for city in remaining) - (len(remaining) - 1)

# Backtracking search for a Hamiltonian path that satisfies flight connections and time window constraints.
# itinerary_so_far is a list of tuples: (city, start_day, end_day)
def backtrack(current_city, visited, current_day):
    if len(visited) == len(durations):
        # All cities have been visited.
        # Check if the current_day exactly equals TOTAL_DAYS.
        if current_day == TOTAL_DAYS:
            return visited
        else:
            return None

    # For each candidate city that is directly reachable from current_city and not yet visited,
    # try to extend the itinerary.
    # Iterate in sorted order for determinism.
    for candidate in sorted(flight_graph[current_city]):
        if candidate in (city for city, _, _ in visited):
            continue

        # Check flight connectivity is satisfied (already ensured by the graph)
        # Determine candidate's arrival interval.
        candidate_start = current_day  # If you fly on current_day, you are in both cities on that day.
        candidate_end = candidate_start + durations[candidate] - 1

        # If candidate has a special event window, ensure its interval covers at least one day in that window.
        if candidate in special_windows:
            window_start, window_end = special_windows[candidate]
            if not interval_intersects(candidate_start, candidate_end, window_start, window_end):
                continue

        # Calculate the new current day after adding candidate.
        new_current_day = candidate_end

        # Determine the remaining cities (set of city names) after choosing candidate.
        remaining = set(durations.keys()) - {city for city, _, _ in visited} - {candidate}
        # Use the minimal additional days needed after candidate.
        if new_current_day + min_additional_days(remaining) > TOTAL_DAYS:
            continue

        new_visited = visited + [(candidate, candidate_start, candidate_end)]
        result = backtrack(candidate, new_visited, new_current_day)
        if result is not None:
            return result

    return None

def main():
    # We know that Geneva must satisfy its special constraint (must be visited when its interval intersects [1,4])
    # For best chance, we force Geneva as the first city.
    start_city = "Geneva"
    start_day = 1
    start_end = start_day + durations[start_city] - 1  # This will be 1 + 4 - 1 = 4
    # Check Geneva's window constraint explicitly (should pass)
    if start_city in special_windows:
        w_start, w_end = special_windows[start_city]
        if not interval_intersects(start_day, start_end, w_start, w_end):
            # If this fails, then no solution exists.
            print(json.dumps({"itinerary": []}))
            return

    initial_visited = [(start_city, start_day, start_end)]
    # Begin backtracking from the start city
    itinerary = backtrack(start_city, initial_visited, start_end)
    if itinerary is None:
        output = {"itinerary": []}
    else:
        # Format the itinerary as required: list of dictionaries with "day_range" and "place"
        # The itinerary list includes a tuple for each city in order.
        formatted = []
        for city, start, end in itinerary:
            day_range = f"Day {start}-{end}"
            formatted.append({"day_range": day_range, "place": city})
        output = {"itinerary": formatted}
    print(json.dumps(output))

if __name__ == "__main__":
    main()