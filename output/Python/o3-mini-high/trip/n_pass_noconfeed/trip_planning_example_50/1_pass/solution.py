#!/usr/bin/env python3
import json

def main():
    # Trip constraints
    total_days = 12
    duration_vilnius = 4
    duration_munich = 3
    duration_mykonos = 7

    # Direct flight connections available: 
    # From Vilnius to Munich and between Munich and Mykonos.
    allowed_flights = {("Vilnius", "Munich"), ("Munich", "Mykonos")}

    # Define the route order and respective durations.
    cities = ["Vilnius", "Munich", "Mykonos"]
    durations = {
        "Vilnius": duration_vilnius,
        "Munich": duration_munich,
        "Mykonos": duration_mykonos
    }

    # Verify flight connectivity for consecutive cities.
    for i in range(len(cities) - 1):
        if (cities[i], cities[i+1]) not in allowed_flights:
            raise ValueError(f"No direct flight available from {cities[i]} to {cities[i+1]}.")

    # Calculate the required total days.
    # If flying from one city to the next, the flight day counts for both cities.
    # Thus, total days needed = sum(durations) - (number of transitions)
    required_days = sum(durations[city] for city in cities) - (len(cities) - 1)
    if required_days != total_days:
        raise ValueError("Trip constraints do not match the total days available.")

    itinerary = []
    current_day = 1
    for i, city in enumerate(cities):
        # Calculate day range for current city
        end_day = current_day + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        # If there is a next city, the flight day is shared
        if i < len(cities) - 1:
            current_day = end_day  # Overlap day for flight transfer

    # Output the itinerary in a JSON-formatted dictionary.
    output = {"itinerary": itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()