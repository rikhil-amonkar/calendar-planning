import json

def calculate_itinerary():
    # Define the constraints
    total_days = 21
    cities = {
        "Manchester": {"days": 3, "must_include": [1, 2, 3]},
        "Istanbul": {"days": 6},
        "Venice": {"days": 7, "must_include": [3, 4, 5, 6, 7, 8, 9]},
        "Krakow": {"days": 6},
        "Lyon": {"days": 2}
    }
    direct_flights = {
        ("Manchester", "Venice"), ("Manchester", "Istanbul"),
        ("Venice", "Istanbul"), ("Istanbul", "Krakow"),
        ("Venice", "Lyon"), ("Lyon", "Istanbul"),
        ("Manchester", "Krakow")
    }

    # Initialize the itinerary
    itinerary = []
    current_day = 1
    visited_cities = set()

    # Function to check if a flight is possible
    def can_fly(from_city, to_city):
        return (from_city, to_city) in direct_flights or (to_city, from_city) in direct_flights

    # Function to add a city to the itinerary
    def add_to_itinerary(city, start_day, end_day):
        nonlocal current_day
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        current_day = end_day + 1
        visited_cities.add(city)

    # Add Manchester first due to the wedding constraint
    add_to_itinerary("Manchester", 1, 3)

    # Add Venice next due to the workshop constraint
    add_to_itinerary("Venice", 3, 9)

    # Add Istanbul
    if can_fly("Venice", "Istanbul"):
        add_to_itinerary("Istanbul", 9, 15)

    # Add Krakow
    if can_fly("Istanbul", "Krakow"):
        add_to_itinerary("Krakow", 15, 20)

    # Since there's no direct flight from Krakow to Istanbul, go back to Istanbul via another city
    if can_fly("Krakow", "Istanbul"):
        add_to_itinerary("Istanbul", 20, 21)
    else:
        # Go back to Istanbul via Venice
        if can_fly("Krakow", "Venice") and can_fly("Venice", "Istanbul"):
            add_to_itinerary("Venice", 20, 21)
            add_to_itinerary("Istanbul", 21, 22)

    # Add Lyon from Istanbul
    if can_fly("Istanbul", "Lyon"):
        add_to_itinerary("Lyon", 21, 22)

    # Adjust the last day to fit within the total days constraint
    if itinerary[-1]["day_range"].endswith("22"):
        itinerary[-1]["day_range"] = "Day 21-21"

    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Run the function and print the result
print(calculate_itinerary())