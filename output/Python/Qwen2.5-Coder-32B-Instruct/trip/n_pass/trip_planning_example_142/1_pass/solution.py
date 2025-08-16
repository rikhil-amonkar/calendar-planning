import json

def calculate_itinerary():
    # Input constraints
    total_days = 7
    days_in_madrid = 4
    days_in_dublin = 3
    days_in_tallinn = 2
    tallinn_workshop_days = range(6, 8)  # Day 6 and Day 7

    # Initialize itinerary
    itinerary = []

    # Start in Madrid for 4 days
    itinerary.append({"day_range": f"Day 1-{days_in_madrid}", "place": "Madrid"})
    current_day = days_in_madrid

    # Fly to Dublin on the same day as the last day in Madrid
    itinerary.append({"day_range": f"Day {current_day}-{current_day + 1}", "place": "Dublin"})
    current_day += 1

    # Stay in Dublin for the remaining days needed
    days_left_in_dublin = days_in_dublin - 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_left_in_dublin}", "place": "Dublin"})
    current_day += days_left_in_dublin

    # Fly to Tallinn on the same day as the last day in Dublin
    itinerary.append({"day_range": f"Day {current_day}-{current_day + 1}", "place": "Tallinn"})
    current_day += 1

    # Stay in Tallinn for the remaining days needed, including the workshop
    days_left_in_tallinn = days_in_tallinn - 1
    itinerary.append({"day_range": f"Day {current_day}-{total_days}", "place": "Tallinn"})

    return itinerary

# Calculate and print the itinerary in JSON format
itinerary_result = {"itinerary": calculate_itinerary()}
print(json.dumps(itinerary_result))