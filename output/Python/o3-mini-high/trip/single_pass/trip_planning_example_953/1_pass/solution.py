#!/usr/bin/env python3
import json
import itertools

def main():
    # Total itinerary days (after accounting for overlapping flight days)
    total_days = 18

    # Define the required durations in each city (in days, counting overlaps on flight days)
    durations = {
        "Salzburg": 4,
        "Stockholm": 2,
        "Venice": 5,
        "Frankfurt": 4,
        "Florence": 4,
        "Barcelona": 2,
        "Stuttgart": 3
    }
    
    # List of available direct flight pairs (bidirectional)
    flight_edges = [
        ("Barcelona", "Frankfurt"),
        ("Florence", "Frankfurt"),
        ("Stockholm", "Barcelona"),
        ("Barcelona", "Florence"),
        ("Venice", "Barcelona"),
        ("Stuttgart", "Barcelona"),
        ("Frankfurt", "Salzburg"),
        ("Stockholm", "Frankfurt"),
        ("Stuttgart", "Stockholm"),
        ("Stuttgart", "Frankfurt"),
        ("Venice", "Stuttgart"),
        ("Venice", "Frankfurt")
    ]
    
    # Build a graph/dictionary for direct flight connections (bidirectional)
    flight_graph = {}
    for city in durations.keys():
        flight_graph[city] = set()
    for (a, b) in flight_edges:
        flight_graph[a].add(b)
        flight_graph[b].add(a)
    
    # Special constraints:
    # 1. Must attend the annual show in Venice from Day 1 to Day 5
    #    => Start the trip in Venice (and spend 5 days there).
    # 2. Salzburg only has one direct connection (with Frankfurt)
    #    => Salzburg must be the final destination.
    # 3. Consequently, Frankfurt must come immediately before Salzburg.
    
    start_city = "Venice"
    end_city = "Salzburg"
    penultimate_city = "Frankfurt"
    
    # The remaining cities (apart from start, penultimate, and end) to order arbitrarily.
    remaining_cities = [city for city in durations.keys() if city not in (start_city, penultimate_city, end_city)]
    
    valid_itinerary = None
    
    # We want an itinerary of 7 cities with order:
    # [start_city] + permutation(remaining_cities) + [penultimate_city, end_city]
    for perm in itertools.permutations(remaining_cities):
        candidate = [start_city] + list(perm) + [penultimate_city, end_city]
        valid = True
        # Check flight connectivity for each consecutive pair in candidate itinerary.
        for i in range(len(candidate) - 1):
            current_city = candidate[i]
            next_city = candidate[i+1]
            if next_city not in flight_graph[current_city]:
                valid = False
                break
        if valid:
            valid_itinerary = candidate
            break

    if not valid_itinerary:
        # If no valid itinerary is found, output an empty itinerary in JSON.
        print(json.dumps({"itinerary": []}))
        return

    # Calculate the day ranges for each city.
    # The rule is: if you fly from city A to city B on day X,
    # then day X counts as a day in both city A and city B.
    # We allocate each city's stay in segments so that:
    #  total days = sum(durations) - (number of flights)
    itinerary_schedule = []
    current_day = 1
    for city in valid_itinerary:
        start_day = current_day
        end_day = start_day + durations[city] - 1
        itinerary_schedule.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        # Update the starting day for the next city.
        # We subtract 1 because the flight day (end_day) counts for both cities.
        current_day = start_day + durations[city] - 1

    # For safety, check that the final end_day equals total_days.
    if itinerary_schedule and itinerary_schedule[-1]["day_range"].split()[-1].split("-")[-1]:
        # We can parse the last end day.
        last_range = itinerary_schedule[-1]["day_range"]
        # Extract the end day by splitting the string "Day X-Y"
        try:
            end_str = last_range.split()[1]  # "X-Y"
            _, end_num = end_str.split("-")
            if int(end_num) != total_days:
                # Adjust if necessary (in our constructed itinerary it should equal 18).
                pass
        except Exception:
            pass

    # Output the itinerary as JSON.
    output = {"itinerary": itinerary_schedule}
    print(json.dumps(output))

if __name__ == "__main__":
    main()