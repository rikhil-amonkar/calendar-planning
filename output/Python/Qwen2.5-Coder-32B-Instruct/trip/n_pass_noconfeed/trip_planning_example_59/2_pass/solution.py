import json

def calculate_itinerary():
    # Input constraints
    total_days = 16
    stay_lyon = 7
    stay_bucharest = 7
    stay_porto = 4
    wedding_days = range(1, 8)  # Day 1 to Day 7 inclusive
    flights = {
        ('Lyon', 'Bucharest'): True,
        ('Bucharest', 'Lyon'): True,
        ('Lyon', 'Porto'): True,
        ('Porto', 'Lyon'): True
    }

    # Initialize itinerary
    itinerary = []

    # Start in Lyon for 7 days
    itinerary.append({"day_range": f"Day 1-{stay_lyon}", "place": "Lyon"})
    current_day = stay_lyon

    # Move to Bucharest for the wedding and stay for 7 days
    itinerary.append({"day_range": f"Day {current_day+1}-{current_day + stay_bucharest}", "place": "Bucharest"})
    current_day += stay_bucharest

    # Move to Porto for the remaining days
    remaining_days = total_days - current_day
    if remaining_days >= stay_porto:
        itinerary.append({"day_range": f"Day {current_day+1}-{current_day + stay_porto}", "place": "Porto"})
    else:
        raise ValueError("Not enough days left to stay in Porto for the required duration.")

    return itinerary

# Calculate and print the itinerary in JSON format
itinerary_result = {"itinerary": calculate_itinerary()}
print(json.dumps(itinerary_result, indent=4))