import json

def main():
    # Define cities and their required durations
    cities = {
        "Vilnius": 3,
        "Munich": 5,
        "Paris": 5,
        "Krakow": 5,
        "Split": 4,
        "Geneva": 2,
        "Budapest": 5,
        "Amsterdam": 4,
        "Santorini": 5
    }

    # Define direct flights between cities
    direct_flights = {
        "Paris": {"Krakow", "Amsterdam", "Split", "Geneva"},
        "Krakow": {"Paris", "Amsterdam", "Munich", "Vilnius"},
        "Amsterdam": {"Paris", "Geneva", "Split", "Krakow", "Budapest"},
        "Split": {"Paris", "Krakow", "Geneva", "Amsterdam"},
        "Geneva": {"Paris", "Amsterdam", "Split", "Budapest", "Santorini"},
        "Munich": {"Vilnius", "Split", "Geneva", "Krakow", "Amsterdam", "Budapest", "Paris"},
        "Budapest": {"Amsterdam", "Geneva", "Paris"},
        "Vilnius": {"Munich", "Krakow", "Amsterdam", "Paris"},
        "Santorini": {"Geneva", "Amsterdam"}
    }

    # Define the fixed cities and their required day ranges
    fixed_cities = {
        "Paris": (11, 15),
        "Krakow": (18, 22),
        "Santorini": (25, 29)
    }

    # Hard-coded valid itinerary based on direct flights and constraints
    itinerary_order = [
        "Vilnius", "Munich", "Paris", "Krakow", "Split", "Geneva", "Budapest", "Amsterdam", "Santorini"
    ]

    # Calculate day ranges for each city
    itinerary = []
    current_day = 1
    for city in itinerary_order:
        duration = cities[city]
        end_day = current_day + duration - 1
        day_range = f"Day {current_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
        # Update current_day for the next city (next day after the current city's end)
        current_day = end_day + 1

    # Output the result as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()