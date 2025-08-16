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
    current_day = 9
    current_city = "Berlin"

    # Move to Tallinn after the conference
    if (current_city, "Tallinn") in direct_flights or ("Tallinn", current_city) in direct_flights:
        itinerary.append({"day_range": f"Day {current_day}-7", "place": "Tallinn"})
        current_day = 8
        current_city = "Tallinn"

    # Visit relatives in Tallinn
    itinerary.append({"day_range": f"Day {relative_visit_days.start}-{relative_visit_days.stop - 1}", "place": "Tallinn"})
    current_day = 13
    current_city = "Tallinn"

    # Adjust the last part of the itinerary to fit the exact days
    if current_day > total_days:
        raise ValueError("Itinerary exceeds the total number of days")

    # If there are remaining days, adjust the itinerary
    if current_day < total_days:
        remaining_days = total_days - current_day + 1
        if (current_city, "Stockholm") in direct_flights or ("Stockholm", current_city) in direct_flights:
            itinerary.append({"day_range": f"Day {current_day}-{current_day + remaining_days - 1}", "place": "Stockholm"})

    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))