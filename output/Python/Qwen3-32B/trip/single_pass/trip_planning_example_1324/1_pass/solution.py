import json

def main():
    # Define the cities and their required durations
    cities = {
        "Tallinn": 5,
        "Munich": 3,
        "Copenhagen": 4,
        "Barcelona": 3,
        "Reykjavik": 4,
        "Athens": 2,
        "Dubrovnik": 5,
        "Venice": 4,
        "Lyon": 4
    }

    # Define the order of cities based on constraints and direct flights
    itinerary_order = ["Tallinn", "Munich", "Copenhagen", "Barcelona", "Reykjavik", "Athens", "Dubrovnik", "Venice", "Lyon"]

    # Calculate day ranges for each city
    itinerary = []
    current_day = 1
    for city in itinerary_order:
        duration = cities[city]
        end_day = current_day + duration - 1
        day_range = f"Day {current_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
        current_day = end_day + 1  # Next city starts the same day the previous ends

    # Output the result as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()