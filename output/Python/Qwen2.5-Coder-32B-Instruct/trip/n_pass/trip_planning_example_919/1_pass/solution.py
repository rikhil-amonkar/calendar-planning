import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Vienna": (1, 5),  # Days 1-5 (inclusive)
        "Milan": (6, 7),   # Days 6-7 (inclusive)
        "Rome": (8, 10),   # Days 8-10 (inclusive)
        "Riga": (11, 12),  # Days 11-12 (inclusive)
        "Lisbon": (11, 13),# Days 11-13 (inclusive)
        "Vilnius": (14, 17),# Days 14-17 (inclusive)
        "Oslo": (13, 15)   # Days 13-15 (inclusive)
    }
    
    # Define the direct flights
    direct_flights = {
        "Riga": ["Oslo", "Milan", "Lisbon", "Rome", "Vienna"],
        "Oslo": ["Riga", "Rome", "Milan", "Vienna", "Lisbon"],
        "Rome": ["Oslo", "Riga", "Milan", "Vienna", "Lisbon"],
        "Milan": ["Oslo", "Riga", "Rome", "Vienna"],
        "Vienna": ["Oslo", "Riga", "Rome", "Milan", "Lisbon", "Vilnius"],
        "Lisbon": ["Oslo", "Riga", "Rome", "Vienna"],
        "Vilnius": ["Vienna", "Riga", "Oslo", "Milan"]
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    current_city = None
    
    # Function to add a stay to the itinerary
    def add_stay(city, start_day, end_day):
        nonlocal current_city
        if current_city != city:
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
            current_city = city
        else:
            last_entry = itinerary[-1]
            last_start, last_end = map(int, last_entry["day_range"].split("-")[1].split("Day ")[1].split("-"))
            if last_end + 1 == start_day:
                last_entry["day_range"] = f"Day {last_start}-{end_day}"
            else:
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
    
    # Process each constraint
    for city, (start_day, end_day) in constraints.items():
        # Find the previous city in the itinerary
        if itinerary:
            last_city = itinerary[-1]["place"]
            if last_city != city and city not in direct_flights[last_city]:
                raise ValueError(f"No direct flight from {last_city} to {city}")
        add_stay(city, start_day, end_day)
        current_day = end_day + 1
    
    # Validate the itinerary
    if current_day != 16:
        raise ValueError("Itinerary does not cover all 15 days")
    
    return itinerary

# Calculate and print the itinerary as JSON
itinerary = calculate_itinerary()
print(json.dumps({"itinerary": itinerary}))