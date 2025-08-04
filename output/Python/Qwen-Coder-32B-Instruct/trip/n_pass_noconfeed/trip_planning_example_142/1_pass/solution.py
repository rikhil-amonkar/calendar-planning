import json

def calculate_itinerary():
    # Input variables
    total_days = 7
    days_in_madrid = 4
    days_in_dublin = 3
    days_in_tallinn = 2
    tallinn_workshop_days = range(6, 8)  # Day 6 and Day 7

    # Initialize itinerary list
    itinerary = []

    # Start in Madrid for the first 4 days
    itinerary.append({"day_range": f"Day 1-{days_in_madrid}", "place": "Madrid"})

    # Move to Dublin on day 5 and stay for 3 days
    start_day_dublin = days_in_madrid
    end_day_dublin = start_day_dublin + days_in_dublin - 1
    itinerary.append({"day_range": f"Day {start_day_dublin}-{end_day_dublin}", "place": "Dublin"})

    # Move to Tallinn on day 6 and stay for 2 days
    start_day_tallinn = end_day_dublin
    end_day_tallinn = start_day_tallinn + days_in_tallinn - 1
    itinerary.append({"day_range": f"Day {start_day_tallinn}-{end_day_tallinn}", "place": "Tallinn"})

    return {"itinerary": itinerary}

# Calculate and print the itinerary in JSON format
print(json.dumps(calculate_itinerary()))