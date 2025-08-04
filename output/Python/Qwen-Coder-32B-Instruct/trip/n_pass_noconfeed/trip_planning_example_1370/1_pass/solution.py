import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Santorini": {"days": 5, "preferred_start": 25, "preferred_end": 29},
        "Krakow": {"days": 5, "preferred_start": 18, "preferred_end": 22},
        "Paris": {"days": 5, "preferred_start": 11, "preferred_end": 15},
        "Vilnius": {"days": 3},
        "Munich": {"days": 5},
        "Geneva": {"days": 2},
        "Amsterdam": {"days": 4},
        "Budapest": {"days": 5},
        "Split": {"days": 4}
    }

    # Define the possible flights
    flights = [
        ("Paris", "Krakow"), ("Paris", "Amsterdam"), ("Paris", "Split"),
        ("Vilnius", "Munich"), ("Paris", "Geneva"), ("Amsterdam", "Geneva"),
        ("Munich", "Split"), ("Split", "Krakow"), ("Munich", "Amsterdam"),
        ("Budapest", "Amsterdam"), ("Split", "Geneva"), ("Vilnius", "Split"),
        ("Munich", "Geneva"), ("Munich", "Krakow"), ("Krakow", "Vilnius"),
        ("Vilnius", "Amsterdam"), ("Budapest", "Paris"), ("Krakow", "Amsterdam"),
        ("Vilnius", "Paris"), ("Budapest", "Geneva"), ("Split", "Amsterdam"),
        ("Santorini", "Geneva"), ("Amsterdam", "Santorini"), ("Munich", "Budapest"),
        ("Munich", "Paris")
    ]

    # Initialize the itinerary
    itinerary = []
    current_day = 1

    # Function to check if a flight is possible
    def can_fly(city1, city2):
        return (city1, city2) in flights or (city2, city1) in flights

    # Function to add a city to the itinerary
    def add_city(city, days):
        nonlocal current_day
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": city})
        current_day += days

    # Add Santorini
    santorini_start = max(25, current_day)
    while current_day < santorini_start:
        # Find a nearby city to stay until Santorini
        for city in constraints:
            if city != "Santorini" and can_fly(itinerary[-1]["place"] if itinerary else "Paris", city):
                add_city(city, min(constraints[city].get("days", 1), santorini_start - current_day))
                break
    add_city("Santorini", 5)

    # Add Krakow
    krakow_start = max(18, current_day)
    while current_day < krakow_start:
        # Find a nearby city to stay until Krakow
        for city in constraints:
            if city != "Krakow" and can_fly(itinerary[-1]["place"], city):
                add_city(city, min(constraints[city].get("days", 1), krakow_start - current_day))
                break
    add_city("Krakow", 5)

    # Add Paris
    paris_start = max(11, current_day)
    while current_day < paris_start:
        # Find a nearby city to stay until Paris
        for city in constraints:
            if city != "Paris" and can_fly(itinerary[-1]["place"], city):
                add_city(city, min(constraints[city].get("days", 1), paris_start - current_day))
                break
    add_city("Paris", 5)

    # Add Vilnius
    add_city("Vilnius", 3)

    # Add Munich
    add_city("Munich", 5)

    # Add Geneva
    add_city("Geneva", 2)

    # Add Amsterdam
    add_city("Amsterdam", 4)

    # Add Budapest
    add_city("Budapest", 5)

    # Add Split
    add_city("Split", 4)

    # Fill remaining days if any
    while current_day <= 30:
        # Find a nearby city to stay until the end
        for city in constraints:
            if can_fly(itinerary[-1]["place"], city):
                add_city(city, 30 - current_day + 1)
                break

    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))