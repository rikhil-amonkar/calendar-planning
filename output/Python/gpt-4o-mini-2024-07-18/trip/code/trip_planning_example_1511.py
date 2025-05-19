import json

def compute_itinerary():
    itinerary = []
    day_counter = 1

    # Venice
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + 2}', 'place': 'Venice'})
    day_counter += 3

    # Munich (Day 4-6 for the annual show)
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + 2}', 'place': 'Munich'})
    day_counter += 3

    # Attend annual show in Munich
    # Add transition from Day 4 - 6 in Munich (which overlaps with the previous stay)
    
    # Reykjavik (after Munich)
    itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Munich', 'to': 'Reykjavik'})
    day_counter += 1
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + 1}', 'place': 'Reykjavik'})
    day_counter += 2

    # Santorini (after Reykjavik)
    itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Reykjavik', 'to': 'Santorini'})
    day_counter += 1
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + 2}', 'place': 'Santorini'})
    day_counter += 3  # Days 8 - 10 are visiting relatives

    # Manchester (after Santorini)
    itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Santorini', 'to': 'Manchester'})
    day_counter += 1
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + 2}', 'place': 'Manchester'})
    day_counter += 3

    # Porto (after Manchester)
    itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Manchester', 'to': 'Porto'})
    day_counter += 1
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + 2}', 'place': 'Porto'})
    day_counter += 3

    # Bucharest (after Porto)
    itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Porto', 'to': 'Bucharest'})
    day_counter += 1
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + 4}', 'place': 'Bucharest'})
    day_counter += 5

    # Tallinn (after Bucharest)
    itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Bucharest', 'to': 'Tallinn'})
    day_counter += 1
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + 3}', 'place': 'Tallinn'})
    day_counter += 4

    # Valencia (after Tallinn)
    itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Tallinn', 'to': 'Valencia'})
    day_counter += 1
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + 1}', 'place': 'Valencia'})
    day_counter += 2  # Days 14 - 15 with workshop

    # Vienna (final destination)
    itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Valencia', 'to': 'Vienna'})
    day_counter += 1
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + 4}', 'place': 'Vienna'})
    day_counter += 5

    return json.dumps(itinerary, indent=4)

if __name__ == "__main__":
    result = compute_itinerary()
    print(result)