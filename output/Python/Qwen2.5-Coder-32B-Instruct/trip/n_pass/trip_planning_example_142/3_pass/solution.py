import json

def calculate_itinerary():
    # Input constraints
    total_days = 7
    days_in_madrid = 3
    days_in_dublin = 3
    days_in_tallinn = 1

    # Initialize itinerary
    itinerary = []

    # Start in Madrid for 3 days
    itinerary.append({"day_range": f"Day 1-{days_in_madrid}", "place": "Madrid"})
    current_day = days_in_madrid

    # Move to Dublin on the next day
    start_day_in_dublin = current_day + 1
    end_day_in_dublin = start_day_in_dublin + days_in_dublin - 1
    itinerary.append({"day_range": f"Day {start_day_in_dublin}-{end_day_in_dublin}", "place": "Dublin"})
    current_day = end_day_in_dublin

    # Move to Tallinn on the next day
    start_day_in_tallinn = current_day + 1
    end_day_in_tallinn = start_day_in_tallinn + days_in_tallinn - 1
    itinerary.append({"day_range": f"Day {start_day_in_tallinn}-{end_day_in_tallinn}", "place": "Tallinn"})

    return itinerary

# Calculate and print the itinerary in JSON format
itinerary_result = {"itinerary": calculate_itinerary()}
print(json.dumps(itinerary_result))