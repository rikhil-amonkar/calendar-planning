import json

def compute_itinerary():
    # Define the cities and their required days
    cities = {
        'Santorini': 3,
        'Valencia': 4,
        'Madrid': 2,
        'Seville': 2,
        'Bucharest': 3,
        'Vienna': 4,
        'Riga': 4,
        'Tallinn': 5,
        'Krakow': 5,
        'Frankfurt': 4
    }

    # Define direct flights between cities
    flights = {
        'Santorini': ['Madrid', 'Bucharest'],
        'Valencia': ['Bucharest', 'Krakow', 'Frankfurt'],
        'Madrid': ['Valencia', 'Seville', 'Bucharest', 'Frankfurt'],
        'Seville': ['Valencia', 'Vienna'],
        'Bucharest': ['Riga', 'Valencia', 'Santorini', 'Madrid', 'Frankfurt'],
        'Vienna': ['Seville', 'Valencia', 'Madrid', 'Krakow', 'Frankfurt', 'Riga'],
        'Riga': ['Tallinn'],
        'Tallinn': [],
        'Krakow': ['Frankfurt'],
        'Frankfurt': ['Tallinn', 'Bucharest', 'Riga', 'Madrid', 'Valencia', 'Vienna']
    }

    # Timing constraints
    madrid_show = (6, 7)
    vienna_wedding = (3, 6)
    riga_conference = (20, 23)
    tallinn_workshop = (23, 27)
    krakow_meeting = (11, 15)

    # Build the itinerary
    itinerary = []

    # Start with Vienna for the wedding
    itinerary.append({'day_range': f'Day {vienna_wedding[0]}-{vienna_wedding[1]}', 'place': 'Vienna'})

    # Fly to Seville
    itinerary.append({'flying': f'Day {vienna_wedding[1]}-{vienna_wedding[1]}', 'from': 'Vienna', 'to': 'Seville'})
    # Stay in Seville
    seville_days = cities['Seville']
    start_day = vienna_wedding[1] + 1
    end_day = start_day + seville_days - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Seville'})

    # Fly to Valencia
    itinerary.append({'flying': f'Day {end_day}-{end_day}', 'from': 'Seville', 'to': 'Valencia'})
    # Stay in Valencia
    valencia_days = cities['Valencia']
    start_day = end_day + 1
    end_day = start_day + valencia_days - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Valencia'})

    # Fly to Madrid
    itinerary.append({'flying': f'Day {end_day}-{end_day}', 'from': 'Valencia', 'to': 'Madrid'})
    # Stay in Madrid (including annual show)
    madrid_days = cities['Madrid']
    start_day = end_day + 1
    end_day = start_day + madrid_days - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Madrid'})

    # Fly to Santorini
    itinerary.append({'flying': f'Day {end_day}-{end_day}', 'from': 'Madrid', 'to': 'Santorini'})
    # Stay in Santorini
    santorini_days = cities['Santorini']
    start_day = end_day + 1
    end_day = start_day + santorini_days - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Santorini'})

    # Fly to Bucharest
    itinerary.append({'flying': f'Day {end_day}-{end_day}', 'from': 'Santorini', 'to': 'Bucharest'})
    # Stay in Bucharest
    bucharest_days = cities['Bucharest']
    start_day = end_day + 1
    end_day = start_day + bucharest_days - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Bucharest'})

    # Fly to Riga
    itinerary.append({'flying': f'Day {end_day}-{end_day}', 'from': 'Bucharest', 'to': 'Riga'})
    # Stay in Riga (including conference)
    riga_days = cities['Riga']
    start_day = end_day + 1
    end_day = start_day + riga_days - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Riga'})

    # Fly to Tallinn
    itinerary.append({'flying': f'Day {end_day}-{end_day}', 'from': 'Riga', 'to': 'Tallinn'})
    # Stay in Tallinn (including workshop)
    tallinn_days = cities['Tallinn']
    start_day = end_day + 1
    end_day = start_day + tallinn_days - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Tallinn'})

    # Fly to Krakow
    itinerary.append({'flying': f'Day {end_day}-{end_day}', 'from': 'Tallinn', 'to': 'Krakow'})
    # Stay in Krakow (including meeting)
    krakow_days = cities['Krakow']
    start_day = end_day + 1
    end_day = start_day + krakow_days - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Krakow'})

    # Fly to Frankfurt
    itinerary.append({'flying': f'Day {end_day}-{end_day}', 'from': 'Krakow', 'to': 'Frankfurt'})
    # Stay in Frankfurt
    frankfurt_days = cities['Frankfurt']
    start_day = end_day + 1
    end_day = start_day + frankfurt_days - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Frankfurt'})

    return itinerary

# Generate the JSON output
itinerary = compute_itinerary()
print(json.dumps(itinerary, indent=2))