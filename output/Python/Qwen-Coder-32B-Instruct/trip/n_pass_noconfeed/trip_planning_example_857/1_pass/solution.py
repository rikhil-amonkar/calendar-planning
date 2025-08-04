import json

def calculate_itinerary():
    # Input constraints
    total_days = 18
    city_stays = {
        "Porto": 2,
        "Geneva": 3,
        "Mykonos": 3,
        "Manchester": 4,
        "Hamburg": 5,
        "Naples": 5,
        "Frankfurt": 2
    }
    specific_days = {
        "Mykonos": (10, 12),
        "Manchester": (15, 18),
        "Frankfurt": (5, 6)
    }
    direct_flights = [
        ("Hamburg", "Frankfurt"), ("Naples", "Mykonos"), ("Hamburg", "Porto"),
        ("Hamburg", "Geneva"), ("Mykonos", "Geneva"), ("Frankfurt", "Geneva"),
        ("Frankfurt", "Porto"), ("Geneva", "Porto"), ("Geneva", "Manchester"),
        ("Naples", "Manchester"), ("Frankfurt", "Naples"), ("Frankfurt", "Manchester"),
        ("Naples", "Geneva"), ("Porto", "Manchester"), ("Hamburg", "Manchester")
    ]

    # Initialize variables
    itinerary = []
    current_day = 1
    current_city = None

    def can_travel(from_city, to_city):
        return (from_city, to_city) in direct_flights or (to_city, from_city) in direct_flights

    def add_to_itinerary(city, days):
        nonlocal current_day, current_city
        if current_city != city:
            if current_city:
                itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": city})
            else:
                itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": city})
            current_day += days
            current_city = city
        else:
            itinerary[-1]["day_range"] = f"Day {current_day - days + 1}-{current_day + days - 1}"
            current_day += days

    # Start planning the itinerary
    # Ensure Frankfurt on day 5-6
    add_to_itinerary("Frankfurt", 2)

    # Ensure Mykonos on day 10-12
    if current_day < 10:
        while current_day < 10:
            # Find a city to stay until day 10
            for city, days in city_stays.items():
                if city not in ["Frankfurt", "Mykonos"] and can_travel(current_city, city):
                    add_to_itinerary(city, min(days, 10 - current_day))
                    break
    add_to_itinerary("Mykonos", 3)

    # Ensure Manchester on day 15-18
    if current_day < 15:
        while current_day < 15:
            # Find a city to stay until day 15
            for city, days in city_stays.items():
                if city not in ["Frankfurt", "Mykonos", "Manchester"] and can_travel(current_city, city):
                    add_to_itinerary(city, min(days, 15 - current_day))
                    break
    add_to_itinerary("Manchester", 4)

    # Fill remaining days
    while current_day <= total_days:
        for city, days in city_stays.items():
            if city not in ["Frankfurt", "Mykonos", "Manchester"] and can_travel(current_city, city):
                remaining_days = total_days - current_day + 1
                add_to_itinerary(city, min(days, remaining_days))
                break

    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Run the function and print the result
print(calculate_itinerary())