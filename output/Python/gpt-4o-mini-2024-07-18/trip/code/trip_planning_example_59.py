import json

def create_itinerary():
    # Input parameters
    total_days = 16
    stay_lyon = 7
    stay_bucharest = 7
    stay_porto = 4

    # Define the itinerary
    itinerary = []

    # Bucharest: Day 1-7
    itinerary.append({'day_range': 'Day 1-7', 'place': 'Bucharest'})

    # Travel from Bucharest to Lyon on Day 7
    itinerary.append({'flying': 'Day 7-7', 'from': 'Bucharest', 'to': 'Lyon'})

    # Lyon: Day 8-14 (7 days)
    itinerary.append({'day_range': 'Day 8-14', 'place': 'Lyon'})

    # Travel from Lyon to Porto on Day 14
    itinerary.append({'flying': 'Day 14-14', 'from': 'Lyon', 'to': 'Porto'})

    # Porto: Day 15-16 (2 days)
    itinerary.append({'day_range': 'Day 15-16', 'place': 'Porto'})

    # Fill in the remaining days in Porto to match total days
    # Adjusting Porto to stay for 4 days
    itinerary[-1]['day_range'] = 'Day 15-18'  # Extending to 4 days

    # Prepare JSON output
    json_output = json.dumps(itinerary, indent=4)
    return json_output

if __name__ == "__main__":
    output = create_itinerary()
    print(output)