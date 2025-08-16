import json

def calculate_itinerary():
    # Define the constraints
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
    events = {
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

    # Initialize the itinerary
    itinerary = []
    current_day = 1
    current_city = None  # Start with no city

    def can_travel(from_city, to_city):
        return (from_city, to_city) in direct_flights or (to_city, from_city) in direct_flights

    def add_to_itinerary(city, start_day, end_day):
        nonlocal current_day, current_city
        if current_city is None or can_travel(current_city, city):
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
            current_day = end_day + 1
            current_city = city
        else:
            raise Exception(f"Cannot travel directly from {current_city} to {city}")

    # Attend Frankfurt event on day 5-6
    add_to_itinerary("Frankfurt", 5, 6)

    # Move to Hamburg after Frankfurt event
    add_to_itinerary("Hamburg", 7, 11)

    # Go to Mykonos for 3 days with a meeting between day 10 and 12
    add_to_itinerary("Mykonos", 10, 12)

    # Go to Naples after Mykonos
    add_to_itinerary("Naples", 13, 15)

    # Go to Manchester for 4 days with a wedding between day 15 and 18
    add_to_itinerary("Manchester", 15, 18)

    # Go to Porto for 2 days
    add_to_itinerary("Porto", 16, 17)

    # Ensure all days are covered
    if current_day != total_days + 1:
        raise Exception("Itinerary does not cover exactly 18 days")

    return {"itinerary": itinerary}

# Calculate and print the itinerary as JSON
print(json.dumps(calculate_itinerary(), indent=2))