import json

def calculate_itinerary():
    # Define the constraints
    total_days = 12
    stay_prague = 2
    stay_berlin = 3
    stay_tallinn = 4
    stay_stockholm = 1
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1

    # Stay in Prague for 2 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_prague - 1}", "place": "Prague"})
    current_day += stay_prague

    # Stay in Berlin for 3 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_berlin - 1}", "place": "Berlin"})
    current_day += stay_berlin

    # Stay in Tallinn for 4 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_tallinn - 1}", "place": "Tallinn"})
    current_day += stay_tallinn

    # Stay in Stockholm for 1 day
    itinerary.append({"day_range": f"Day {current_day}", "place": "Stockholm"})
    current_day += stay_stockholm

    # Ensure the itinerary covers exactly 12 days
    assert current_day == total_days + 1, "Itinerary does not cover exactly 12 days"

    return {"itinerary": itinerary}

# Calculate and print the itinerary
try:
    print(json.dumps(calculate_itinerary(), indent=4))
except ValueError as e:
    print(e)