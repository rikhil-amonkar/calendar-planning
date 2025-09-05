#!/usr/bin/env python3
import json

def dfs(itinerary, visited, next_start, graph, durations):
    # Global pruning based on event constraints for cities not yet visited.
    # Wedding in Mykonos must be attended on or before day 3.
    if "Mykonos" not in visited and next_start > 3:
        return None
    # Relatives in Prague must be visited with an overlap of days 7-9.
    if "Prague" not in visited and next_start > 9:
        return None

    # If all cities are visited, return the complete itinerary.
    if len(visited) == len(durations):
        return itinerary

    # If itinerary is empty, choose a valid starting city.
    # Based on the event constraints, starting city must be either Mykonos or Nice.
    if not itinerary:
        for city in ["Mykonos", "Nice"]:
            s = next_start  # which is 1 for the first city
            e = s + durations[city] - 1
            # Check individual event constraints:
            if city == "Mykonos" and s > 3:
                continue  # Wedding in Mykonos must be within day 1-3.
            if city == "Prague":
                # Prague must include at least one day in [7,9]
                if e < 7 or s > 9:
                    continue
            new_itinerary = itinerary + [(city, s, e)]
            new_visited = visited | {city}
            result = dfs(new_itinerary, new_visited, e, graph, durations)
            if result is not None:
                return result
        return None
    else:
        current_city = itinerary[-1][0]
        for candidate in durations:
            if candidate in visited:
                continue
            # Must have a direct flight from the current city to the candidate.
            if candidate not in graph[current_city]:
                continue
            s = next_start
            e = s + durations[candidate] - 1

            # Check event constraints on the candidate city.
            if candidate == "Mykonos" and s > 3:
                continue  # Wedding in Mykonos must happen early.
            if candidate == "Prague":
                # Prague's stay must include at least one day between 7 and 9.
                if e < 7 or s > 9:
                    continue

            new_itinerary = itinerary + [(candidate, s, e)]
            new_visited = visited | {candidate}
            result = dfs(new_itinerary, new_visited, e, graph, durations)
            if result is not None:
                return result
        return None

def main():
    # Define the duration (in days) required in each city.
    durations = {
        "Valencia": 5,
        "Riga": 5,
        "Prague": 3,
        "Mykonos": 3,
        "Zurich": 5,
        "Bucharest": 5,
        "Nice": 2
    }

    # Define the direct flight connections (bidirectional).
    graph = {
        "Mykonos": ["Nice", "Zurich"],
        "Nice": ["Mykonos", "Riga", "Zurich"],
        "Zurich": ["Mykonos", "Prague", "Riga", "Bucharest", "Valencia", "Nice"],
        "Prague": ["Bucharest", "Riga", "Valencia", "Zurich"],
        "Bucharest": ["Prague", "Valencia", "Riga", "Zurich"],
        "Valencia": ["Bucharest", "Prague", "Zurich"],
        "Riga": ["Nice", "Zurich", "Bucharest", "Prague"]
    }

    # Start the DFS search.
    # The first city starts on Day 1.
    itinerary = dfs([], set(), 1, graph, durations)

    # Format the found itinerary as a list of dictionaries.
    output_itinerary = []
    if itinerary:
        for city, start, end in itinerary:
            day_range = "Day {}-{}".format(start, end)
            output_itinerary.append({"day_range": day_range, "place": city})
    result = {"itinerary": output_itinerary}

    # Output the result as valid JSON.
    print(json.dumps(result))

if __name__ == "__main__":
    main()