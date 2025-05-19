import json

def compute_itinerary():
    cities_order = ['Helsinki', 'Reykjavik', 'Madrid', 'Budapest', 'Warsaw', 'Split']
    city_days = {
        'Helsinki': 2,
        'Reykjavik': 2,
        'Madrid': 4,
        'Budapest': 4,
        'Warsaw': 3,
        'Split': 4
    }

    itinerary = []
    current_day = 1

    for i in range(len(cities_order)):
        city = cities_order[i]
        days = city_days[city]
        end_day = current_day + days - 1
        itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': city})

        if i < len(cities_order) - 1:
            next_city = cities_order[i + 1]
            flight_day = end_day
            itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': city, 'to': next_city})
            current_day = flight_day
        else:
            current_day = end_day + 1

    return itinerary

itinerary = compute_itinerary()
print(json.dumps(itinerary, indent=2))