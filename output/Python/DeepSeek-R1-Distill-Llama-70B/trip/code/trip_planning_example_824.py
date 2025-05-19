import json

def compute_itinerary():
    # Define the cities and their required days
    cities = {
        'Berlin': 5,
        'Split': 3,
        'Bucharest': 3,
        'Riga': 5,
        'Lisbon': 3,
        'Tallinn': 4,
        'Lyon': 5
    }

    # Define direct flights between cities
    flights = {
        'Berlin': ['Split', 'Lisbon', 'Riga', 'Tallinn'],
        'Split': ['Lyon'],
        'Bucharest': ['Riga'],
        'Riga': ['Tallinn'],
        'Lisbon': ['Bucharest', 'Riga'],
        'Tallinn': [],
        'Lyon': ['Lisbon', 'Bucharest']
    }

    # Timing constraints
    berlin_show = (1, 5)
    lyon_wedding = (7, 11)
    bucharest_visit = (13, 15)

    # Build the itinerary
    itinerary = []

    # Start with Berlin for the annual show
    itinerary.append({'day_range': f'Day {berlin_show[0]}-{berlin_show[1]}', 'place': 'Berlin'})

    # Fly to Split
    itinerary.append({'flying': f'Day {berlin_show[1]}-{berlin_show[1]}', 'from': 'Berlin', 'to': 'Split'})
    # Stay in Split
    split_days = cities['Split']
    start_day = berlin_show[1] + 1
    end_day = start_day + split_days - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Split'})

    # Fly to Lyon
    itinerary.append({'flying': f'Day {end_day}-{end_day}', 'from': 'Split', 'to': 'Lyon'})
    # Stay in Lyon (including wedding)
    lyon_days = cities['Lyon']
    start_day = end_day + 1
    end_day = start_day + lyon_days - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Lyon'})

    # Fly to Lisbon
    itinerary.append({'flying': f'Day {end_day}-{end_day}', 'from': 'Lyon', 'to': 'Lisbon'})
    # Stay in Lisbon
    lisbon_days = cities['Lisbon']
    start_day = end_day + 1
    end_day = start_day + lisbon_days - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Lisbon'})

    # Fly to Bucharest
    itinerary.append({'flying': f'Day {end_day}-{end_day}', 'from': 'Lisbon', 'to': 'Bucharest'})
    # Stay in Bucharest (including relatives visit)
    bucharest_days = cities['Bucharest']
    start_day = end_day + 1
    end_day = start_day + bucharest_days - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Bucharest'})

    # Fly to Riga
    itinerary.append({'flying': f'Day {end_day}-{end_day}', 'from': 'Bucharest', 'to': 'Riga'})
    # Stay in Riga
    riga_days = cities['Riga']
    start_day = end_day + 1
    end_day = start_day + riga_days - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Riga'})

    # Fly to Tallinn
    itinerary.append({'flying': f'Day {end_day}-{end_day}', 'from': 'Riga', 'to': 'Tallinn'})
    # Stay in Tallinn
    tallinn_days = cities['Tallinn']
    start_day = end_day + 1
    end_day = start_day + tallinn_days - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Tallinn'})

    return itinerary

# Generate the JSON output
itinerary = compute_itinerary()
print(json.dumps(itinerary, indent=2))