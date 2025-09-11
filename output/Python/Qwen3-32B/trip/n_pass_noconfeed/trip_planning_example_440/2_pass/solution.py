import json

def plan_trip():
    # Define cities and their required days
    cities = {
        "Geneva": 6,
        "Split": 2,
        "Helsinki": 2,
        "Vilnius": 3,
        "Reykjavik": 3
    }

    # Direct flights between cities
    direct_flights = {
        "Split": ["Helsinki", "Geneva", "Vilnius"],
        "Helsinki": ["Split", "Geneva", "Reykjavik", "Vilnius"],
        "Geneva": ["Split", "Helsinki"],
        "Vilnius": ["Helsinki", "Split"],
        "Reykjavik": ["Helsinki"]
    }

    # Determine the order of cities
    itinerary_order = ["Geneva", "Split", "Vilnius", "Helsinki", "Reykjavik"]

    # Calculate the day ranges for each city
    day_ranges = []
    current_day = 1

    for city in itinerary_order:
        days_in_city = cities[city]
        day_ranges.append((current_day, current_day + days_in_city - 1))
        current_day += days_in_city

    # Build the itinerary
    itinerary = []
    for i, city in enumerate(itinerary_order):
        start, end = day_ranges[i]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})

    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    plan_trip()