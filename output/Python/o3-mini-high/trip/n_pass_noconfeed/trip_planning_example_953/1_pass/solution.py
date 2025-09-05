import json

# Define the flight graph as a dictionary with sets of directly connected cities.
flight_graph = {
    "Barcelona": {"Frankfurt", "Florence", "Stockholm", "Venice", "Stuttgart"},
    "Frankfurt": {"Barcelona", "Florence", "Salzburg", "Stockholm", "Stuttgart", "Venice"},
    "Florence": {"Frankfurt", "Barcelona"},
    "Stockholm": {"Barcelona", "Frankfurt", "Stuttgart"},
    "Salzburg": {"Frankfurt"},
    "Stuttgart": {"Barcelona", "Stockholm", "Frankfurt", "Venice"},
    "Venice": {"Barcelona", "Stuttgart", "Frankfurt"}
}

# Required stay durations for each city.
stay_durations = {
    "Salzburg": 4,
    "Stockholm": 2,
    "Venice": 5,     # Also covers annual show from Day 1-5.
    "Frankfurt": 4,
    "Florence": 4,
    "Barcelona": 2,
    "Stuttgart": 3
}

# List of all cities.
cities = list(stay_durations.keys())

def find_itinerary(current_city, visited, path):
    # If we have visited all cities, return the current path.
    if len(path) == len(cities):
        return path

    # Iterate over neighbors sorted alphabetically for deterministic behavior.
    for neighbor in sorted(flight_graph[current_city]):
        if neighbor not in visited:
            visited.add(neighbor)
            path.append(neighbor)
            result = find_itinerary(neighbor, visited, path)
            if result is not None:
                return result
            path.pop()
            visited.remove(neighbor)
    return None

def compute_day_ranges(itinerary, durations):
    # For each city in the itinerary compute the day range.
    # Rule: if flying from city A to city B on day X, then day X counts for both cities.
    segments = []
    current_day = 1
    for city in itinerary:
        start_day = current_day
        end_day = start_day + durations[city] - 1
        segments.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        # The flight happens on the last day of the current city so next city's start is the same day.
        current_day = end_day
    return segments

def main():
    # The annual show necessitates being in Venice from Day 1 to Day 5.
    # So we fix Venice as the starting city.
    start_city = "Venice"
    visited = set([start_city])
    path = [start_city]
    
    itinerary_path = find_itinerary(start_city, visited, path)
    
    # If no valid itinerary is found, output an error in JSON.
    if itinerary_path is None:
        print(json.dumps({"error": "No valid itinerary found."}))
        return

    # Compute the day ranges for each city's stay.
    itinerary_segments = compute_day_ranges(itinerary_path, stay_durations)
    
    # Assemble the result dictionary and output it as JSON.
    result = {"itinerary": itinerary_segments}
    print(json.dumps(result))

if __name__ == "__main__":
    main()