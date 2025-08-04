import json

def calculate_itinerary():
    # Define the constraints
    total_days = 12
    stay_prague = 2
    stay_berlin = 3
    conference_days = [6, 8]
    stay_tallinn = 5
    relative_visit_days = range(8, 13)
    stay_stockholm = 5
    direct_flights = {
        ('Berlin', 'Tallinn'), ('Prague', 'Tallinn'), ('Stockholm', 'Tallinn'),
        ('Prague', 'Stockholm'), ('Stockholm', 'Berlin')
    }

    # Initialize the itinerary
    itinerary = []
    current_day = 1
    current_city = None

    # Stay in Prague for 2 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_prague - 1}", "place": "Prague"})
    current_day += stay_prague
    current_city = "Prague"

    # Move to Berlin for the conference days
    if (current_city, "Berlin") in direct_flights or ("Berlin", current_city) in direct_flights:
        itinerary.append({"day_range": f"Day {current_day}-5", "place": "Berlin"})
        current_day = 6
        current_city = "Berlin"

    # Conference days in Berlin
    itinerary.append({"day_range": f"Day {conference_days[0]}-{conference_days[-1]}", "place": "Berlin"})
    current_day = 9  # After conference days
    current_city = "Berlin"

    # Move to Tallinn after the conference
    if (current_city, "Tallinn") in direct_flights or ("Tallinn", current_city) in direct_flights:
        itinerary.append({"day_range": f"Day {current_day}-7", "place": "Tallinn"})
        current_day = 8
        current_city = "Tallinn"

    # Visit relatives in Tallinn
    itinerary.append({"day_range": f"Day {relative_visit_days.start}-{relative_visit_days.stop - 1}", "place": "Tallinn"})
    current_day = 12  # Adjusted to fit within the total days

    # Ensure the itinerary covers exactly 12 days
    if current_day < total_days:
        remaining_days = total_days - current_day
        if (current_city, "Stockholm") in direct_flights or ("Stockholm", current_city) in direct_flights:
            itinerary.append({"day_range": f"Day {current_day + 1}-{total_days}", "place": "Stockholm"})

    return {"itinerary": itinerary}

# Calculate and print the itinerary
try:
    print(json.dumps(calculate_itinerary(), indent=4))
except ValueError as e:
    print(e)