import json

def main():
    # Total trip days
    total_days = 18

    # Define the cities and required durations
    # Note: When flying on the transition day, that day is counted for both cities.
    # This allows the effective timeline to be: sum(durations) - (number of transitions) = 25 - 7 = 18 days.
    city_durations = {
        "Oslo": 2,        # Must include a meeting with friends between Day 1 and Day 2.
        "Dubrovnik": 3,   # Must cover the annual show from Day 2 to Day 4.
        "Helsinki": 2,
        "Vilnius": 2,
        "Krakow": 5,
        "Paris": 2,
        "Madrid": 5,
        "Mykonos": 4      # Relatives are to be visited in Mykonos between Day 15 and Day 18.
    }
    
    # Pre-determined itinerary order based on flight connectivity needs.
    # The planned order is: Oslo -> Dubrovnik -> Helsinki -> Vilnius -> Krakow -> Paris -> Madrid -> Mykonos
    itinerary_order = ["Oslo", "Dubrovnik", "Helsinki", "Vilnius", "Krakow", "Paris", "Madrid", "Mykonos"]

    # Define direct flights as an undirected graph.
    direct_flights = {
        "Oslo": {"Krakow", "Paris", "Madrid", "Helsinki", "Dubrovnik", "Vilnius"},
        "Krakow": {"Oslo", "Paris", "Vilnius", "Helsinki"},  # "from Krakow to Vilnius" is assumed bidirectional.
        "Paris": {"Oslo", "Madrid", "Krakow", "Helsinki", "Vilnius"},
        "Madrid": {"Paris", "Oslo", "Dubrovnik", "Helsinki", "Mykonos"},
        "Helsinki": {"Vilnius", "Oslo", "Krakow", "Dubrovnik", "Paris", "Madrid"},
        "Vilnius": {"Helsinki", "Oslo", "Paris", "Krakow"},
        "Dubrovnik": {"Helsinki", "Madrid", "Oslo"},
        "Mykonos": {"Madrid"}
    }

    # Verify direct flight connectivity for consecutive cities in our itinerary_order.
    for i in range(len(itinerary_order) - 1):
        city_from = itinerary_order[i]
        city_to = itinerary_order[i + 1]
        if city_to not in direct_flights.get(city_from, set()):
            print(json.dumps({
                "error": f"No direct flight from {city_from} to {city_to}."
            }))
            return

    # Compute the itinerary with overlapping flight days.
    itinerary = []
    current_start = 1
    for city in itinerary_order:
        duration = city_durations[city]
        # If flying on the transition day, the arrival city's start day is the same as the previous
        # city's end day (overlap the flight day).
        current_end = current_start + duration - 1
        itinerary.append({"day_range": f"Day {current_start}-{current_end}", "place": city})
        # Next city starts on the same day as current_end because flight day overlaps.
        current_start = current_end

    # Check that the final day matches total_days.
    final_range = itinerary[-1]["day_range"]
    # Extract the end day from the string "Day X-Y"
    final_day = int(final_range.split('-')[1])
    if final_day != total_days:
        print(json.dumps({
            "error": "The computed itinerary does not fill the total day constraint."
        }))
        return

    # Output the itinerary as a JSON-formatted dictionary
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()