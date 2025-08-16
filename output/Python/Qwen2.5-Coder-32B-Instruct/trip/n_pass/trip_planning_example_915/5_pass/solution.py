import json

def calculate_itinerary():
    # Define the constraints
    total_days = 26
    fixed_stays = {
        "Bucharest": 3,
        "Venice": 5,
        "Prague": 4,
        "Frankfurt": 5,
        "Zurich": 5,
        "Florence": 5,
        "Tallinn": 5
    }
    events = {
        "Venice": (22, 26),
        "Frankfurt": (12, 16),
        "Tallinn": (8, 12)
    }
    direct_flights = [
        ("Prague", "Tallinn"), ("Prague", "Zurich"), ("Florence", "Prague"),
        ("Frankfurt", "Bucharest"), ("Frankfurt", "Venice"), ("Prague", "Bucharest"),
        ("Bucharest", "Zurich"), ("Tallinn", "Frankfurt"), ("Zurich", "Florence"),
        ("Frankfurt", "Zurich"), ("Zurich", "Venice"), ("Florence", "Frankfurt"),
        ("Prague", "Frankfurt"), ("Tallinn", "Zurich")
    ]

    # Initialize the itinerary
    itinerary = []
    current_day = 1
    visited_cities = set()

    # Helper function to add a stay to the itinerary
    def add_stay(city, days):
        nonlocal current_day
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": city})
        current_day += days
        visited_cities.add(city)

    # Handle fixed stays with events first
    for city, (start, end) in events.items():
        if city in fixed_stays:
            # Adjust the start day if it's earlier than the current day
            start_day = max(current_day, start)
            # Calculate the number of days to stay
            days_to_stay = min(fixed_stays[city], end - start_day + 1)
            # Move current_day to the start_day if necessary
            if current_day < start_day:
                current_day = start_day
            # Add the stay
            add_stay(city, days_to_stay)

    # Handle other fixed stays
    for city, days in fixed_stays.items():
        if city not in visited_cities:
            # Ensure we do not exceed total_days
            if current_day + days > total_days:
                days = total_days - current_day + 1
            add_stay(city, days)

    # If the itinerary is not complete, fill in remaining days with available cities
    while current_day <= total_days:
        for city in fixed_stays.keys():
            if city not in visited_cities:
                # Check if there's a direct flight from the last visited city
                if not itinerary or any((itinerary[-1]["place"], city) in direct_flights or (city, itinerary[-1]["place"]) in direct_flights):
                    # Ensure we do not exceed total_days
                    days_to_add = min(fixed_stays[city], total_days - current_day + 1)
                    add_stay(city, days_to_add)
                    break

    # Ensure the itinerary covers exactly 26 days
    if current_day > total_days:
        # Remove the last entry if it exceeds 26 days
        last_entry = itinerary.pop()
        days_to_remove = current_day - total_days
        new_days = fixed_stays[last_entry["place"]] - days_to_remove
        if new_days > 0:
            add_stay(last_entry["place"], new_days)

    # Ensure the itinerary is sorted by day_range
    itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))

    # Final check to ensure no overlaps and exact coverage
    if len(itinerary) > 1:
        for i in range(1, len(itinerary)):
            prev_end = int(itinerary[i-1]["day_range"].split('-')[1])
            current_start = int(itinerary[i]["day_range"].split('-')[0].split()[1])
            if prev_end >= current_start:
                raise ValueError("Itinerary has overlapping days")

    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))