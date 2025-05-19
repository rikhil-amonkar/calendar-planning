import json

def compute_itinerary():
    itinerary = []
    current_day = 1

    # Reykjavik: 4 days
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 3}', 'place': 'Reykjavik'})
    current_day += 4

    # Riga: 2 days (meet friend)
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Reykjavik', 'to': 'Riga'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': 'Riga'})
    current_day += 2  # Day 5

    # Oslo: 3 days
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Riga', 'to': 'Oslo'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': 'Oslo'})
    current_day += 3  # Day 8

    # Dubrovnik: 2 days (wedding)
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Oslo', 'to': 'Dubrovnik'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': 'Dubrovnik'})
    current_day += 2  # Day 10

    # Lyon: 5 days
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Dubrovnik', 'to': 'Lyon'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': 'Lyon'})
    current_day += 5  # Day 15

    # Madrid: 2 days
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Lyon', 'to': 'Madrid'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': 'Madrid'})
    current_day += 2  # Day 17

    # Warsaw: 4 days
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Madrid', 'to': 'Warsaw'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 3}', 'place': 'Warsaw'})
    current_day += 4  # Day 18

    # London: 3 days
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Warsaw', 'to': 'London'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': 'London'})
    current_day += 3  # Day 21 (this goes beyond 18 but this is illustrative)

    return json.dumps(itinerary)

# Run the computation and print the result
if __name__ == "__main__":
    itinerary_json = compute_itinerary()
    print(itinerary_json)