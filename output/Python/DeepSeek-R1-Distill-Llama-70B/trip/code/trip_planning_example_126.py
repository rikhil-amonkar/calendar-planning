import json

def compute_itinerary():
    # Define the cities and their required days
    cities = {
        'Krakow': 5,
        'Paris': 2,
        'Seville': 6
    }

    # Define direct flights between cities
    flights = {
        'Krakow': ['Paris'],
        'Paris': ['Seville'],
        'Seville': []
    }

    # Timing constraints
    krakow_workshop = (1, 5)

    # Build the itinerary
    itinerary = []

    # Start with Krakow for the workshop
    itinerary.append({'day_range': f'Day {krakow_workshop[0]}-{krakow_workshop[1]}', 'place': 'Krakow'})

    # Fly to Paris
    itinerary.append({'flying': f'Day {krakow_workshop[1]}-{krakow_workshop[1]}', 'from': 'Krakow', 'to': 'Paris'})
    # Stay in Paris
    paris_days = cities['Paris']
    start_day = krakow_workshop[1] + 1
    end_day = start_day + paris_days - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Paris'})

    # Fly to Seville
    itinerary.append({'flying': f'Day {end_day}-{end_day}', 'from': 'Paris', 'to': 'Seville'})
    # Stay in Seville
    seville_days = cities['Seville']
    start_day = end_day + 1
    end_day = start_day + seville_days - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Seville'})

    return itinerary

# Generate the JSON output
itinerary = compute_itinerary()
print(json.dumps(itinerary, indent=2))