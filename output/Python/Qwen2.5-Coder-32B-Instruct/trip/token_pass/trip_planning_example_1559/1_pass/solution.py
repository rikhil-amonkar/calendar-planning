import json

def create_itinerary():
    # Define the constraints
    constraints = {
        "Valencia": {"days": 2, "specific_days": (3, 4)},
        "Oslo": {"days": 3, "specific_days": (13, 15)},
        "Lyon": {"days": 4, "specific_days": None},
        "Prague": {"days": 3, "specific_days": None},
        "Paris": {"days": 4, "specific_days": None},
        "Nice": {"days": 4, "specific_days": None},
        "Seville": {"days": 5, "specific_days": (5, 9)},
        "Tallinn": {"days": 2, "specific_days": None},
        "Mykonos": {"days": 5, "specific_days": (21, 25)},
        "Lisbon": {"days": 2, "specific_days": None}
    }

    # Define direct flight connections
    flights = [
        ("Lisbon", "Paris"), ("Lyon", "Nice"), ("Tallinn", "Oslo"),
        ("Prague", "Lyon"), ("Paris", "Oslo"), ("Lisbon", "Seville"),
        ("Prague", "Lisbon"), ("Oslo", "Nice"), ("Valencia", "Paris"),
        ("Valencia", "Lisbon"), ("Paris", "Nice"), ("Nice", "Mykonos"),
        ("Paris", "Lyon"), ("Valencia", "Lyon"), ("Prague", "Oslo"),
        ("Prague", "Paris"), ("Seville", "Paris"), ("Oslo", "Lyon"),
        ("Prague", "Valencia"), ("Lisbon", "Nice"), ("Lisbon", "Oslo"),
        ("Valencia", "Seville"), ("Lisbon", "Lyon"), ("Paris", "Tallinn"),
        ("Prague", "Tallinn")
    ]

    # Initialize the itinerary
    itinerary = []
    current_day = 1

    # Add fixed events first
    def add_event(city, start_day, end_day):
        nonlocal current_day
        if current_day <= start_day:
            current_day = start_day
        else:
            raise ValueError(f"Overlap detected for {city} from Day {start_day}-{end_day}")
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": city})
        current_day = end_day + 1

    # Add Seville event
    add_event("Seville", 5, 9)

    # Add Valencia event
    add_event("Valencia", 3, 4)

    # Add Oslo event
    add_event("Oslo", 13, 15)

    # Add Mykonos event
    add_event("Mykonos", 21, 25)

    # Function to find a direct flight to a city
    def can_fly_to(current_city, target_city):
        return (current_city, target_city) in flights or (target_city, current_city) in flights

    # Helper function to find the next city to visit
    def find_next_city(current_city, remaining_cities):
        for city in remaining_cities:
            if can_fly_to(current_city, city):
                return city
        return None

    # Remaining cities to visit
    remaining_cities = set(constraints.keys()) - {event["place"] for event in itinerary}

    # Current city is the last added event's place
    current_city = itinerary[-1]["place"]

    # Fill in the remaining days
    while remaining_cities and current_day <= 25:
        next_city = find_next_city(current_city, remaining_cities)
        if next_city is None:
            raise ValueError(f"No direct flight available from {current_city} to any remaining city")
        
        days_to_stay = constraints[next_city]["days"]
        if current_day + days_to_stay > 25:
            raise ValueError(f"Not enough days left to visit {next_city}")
        
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days_to_stay - 1}", "place": next_city})
        current_day += days_to_stay
        remaining_cities.remove(next_city)
        current_city = next_city

    # Validate the itinerary
    if current_day != 26:
        raise ValueError("Itinerary does not cover exactly 25 days")

    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Run the function and print the result
print(create_itinerary())