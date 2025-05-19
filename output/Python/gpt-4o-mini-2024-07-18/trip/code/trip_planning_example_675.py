import json

def calculate_itinerary():
    itinerary = []

    # Setting initial days
    current_day = 1

    # Dubrovnik for 4 days
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 3}', 'place': 'Dubrovnik'})
    current_day += 4

    # Munich for 5 days with an annual show from day 4 to day 8
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Dubrovnik', 'to': 'Munich'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': 'Munich'})
    current_day += 5

    # Krakow for 2 days with friends between day 8 and 9
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Munich', 'to': 'Krakow'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': 'Krakow'})
    current_day += 2

    # Split for 3 days
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Krakow', 'to': 'Split'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': 'Split'})
    current_day += 3

    # Milan for 3 days with a wedding between day 11 and 13
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Split', 'to': 'Milan'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': 'Milan'})
    current_day += 3

    # Porto for 4 days
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Milan', 'to': 'Porto'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 3}', 'place': 'Porto'})
    current_day += 4

    # Finalize the itinerary for JSON output
    return json.dumps(itinerary, indent=4)

if __name__ == "__main__":
    result = calculate_itinerary()
    print(result)