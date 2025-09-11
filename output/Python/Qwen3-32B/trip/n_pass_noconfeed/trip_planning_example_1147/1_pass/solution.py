import json

def main():
    # Define cities and required days
    cities = {
        "Istanbul": 5,
        "Brussels": 3,
        "Milan": 4,
        "Split": 4,
        "Helsinki": 3,
        "Frankfurt": 3,
        "Dubrovnik": 2,
        "Vilnius": 5
    }

    # Direct flight connections (bidirectional)
    direct_flights = {
        "Milan": ["Frankfurt", "Split"],
        "Split": ["Frankfurt", "Milan", "Helsinki", "Vilnius"],
        "Brussels": ["Vilnius", "Helsinki", "Milan", "Frankfurt"],
        "Helsinki": ["Vilnius", "Dubrovnik", "Brussels", "Split", "Frankfurt"],
        "Istanbul": ["Brussels", "Helsinki", "Milan"],
        "Vilnius": ["Brussels", "Helsinki", "Split", "Frankfurt"],
        "Frankfurt": ["Milan", "Split", "Brussels", "Helsinki", "Dubrovnik", "Vilnius"],
        "Dubrovnik": ["Frankfurt", "Helsinki"]
    }

    # Constraints
    constraints = {
        "Istanbul": {"start_day": 1, "end_day": 5},
        "Frankfurt": {"start_day": 16, "end_day": 18},
        "Vilnius": {"start_day": 18, "end_day": 22}
    }

    # Optimal itinerary sequence
    itinerary_sequence = [
        "Istanbul", "Brussels", "Milan", "Split", "Helsinki", "Frankfurt", "Dubrovnik", "Vilnius"
    ]

    # Calculate day ranges
    itinerary = []
    current_day = 1

    for city in itinerary_sequence:
        duration = cities[city]
        end_day = current_day + duration - 1
        itinerary.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        current_day = end_day

    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()