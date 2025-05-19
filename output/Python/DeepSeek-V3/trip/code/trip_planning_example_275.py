import json

def calculate_itinerary():
    # Input parameters
    total_days = 14
    city_days = {
        'Split': 5,
        'Vilnius': 4,
        'Santorini': 2,
        'Madrid': 6
    }
    conference_days = [13, 14]
    conference_city = 'Santorini'
    direct_flights = {
        'Vilnius': ['Split'],
        'Split': ['Vilnius', 'Madrid'],
        'Madrid': ['Split', 'Santorini'],
        'Santorini': ['Madrid']
    }

    # Initialize itinerary
    itinerary = []
    current_day = 1

    # Determine the order of cities
    # Santorini must be last (days 13-14)
    # We need to visit Split, Vilnius, Madrid, and Santorini
    # Possible sequences considering direct flights:
    # 1. Vilnius -> Split -> Madrid -> Santorini
    # 2. Split -> Vilnius -> Split -> Madrid -> Santorini
    # But we have only 14 days, so option 1 is better

    # Check if all cities can be visited with the given constraints
    required_days = sum(city_days.values())
    if required_days > total_days:
        return {"error": "Not enough days to visit all cities"}

    # Sequence: Vilnius -> Split -> Madrid -> Santorini
    sequence = ['Vilnius', 'Split', 'Madrid', 'Santorini']

    # Verify if the sequence is possible with direct flights
    for i in range(len(sequence) - 1):
        if sequence[i+1] not in direct_flights[sequence[i]]:
            return {"error": "No direct flight between cities in the sequence"}

    # Assign days to each city
    for city in sequence:
        if city == conference_city:
            # Santorini days are fixed (13-14)
            days = city_days[city]
            if [current_day, current_day + days - 1] != [13, 14]:
                return {"error": "Santorini must be on days 13-14"}
            itinerary.append({
                'day_range': f'Day {current_day}-{current_day + days - 1}',
                'place': city
            })
            current_day += days
        else:
            days = city_days[city]
            itinerary.append({
                'day_range': f'Day {current_day}-{current_day + days - 1}',
                'place': city
            })
            current_day += days
            # Add flight to next city if not last city
            if city != sequence[-1]:
                next_city = sequence[sequence.index(city) + 1]
                itinerary.append({
                    'flying': f'Day {current_day - 1}-{current_day - 1}',
                    'from': city,
                    'to': next_city
                })

    return itinerary

itinerary = calculate_itinerary()
print(json.dumps(itinerary, indent=2))