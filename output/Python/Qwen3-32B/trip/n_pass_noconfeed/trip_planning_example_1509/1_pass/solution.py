import json

def main():
    # Define the cities and their constraints
    cities = {
        'Paris': {'duration': 5, 'constraint': (4, 8)},
        'Warsaw': {'duration': 2, 'constraint': None},
        'Krakow': {'duration': 2, 'constraint': (17, 18)},
        'Tallinn': {'duration': 2, 'constraint': None},
        'Riga': {'duration': 2, 'constraint': (23, 24)},
        'Copenhagen': {'duration': 5, 'constraint': None},
        'Helsinki': {'duration': 5, 'constraint': (18, 22)},
        'Oslo': {'duration': 5, 'constraint': None},
        'Santorini': {'duration': 2, 'constraint': (12, 13)},
        'Lyon': {'duration': 4, 'constraint': None},
    }

    # Define direct flights (bidirectional)
    direct_flights = {
        ('Warsaw', 'Riga'), ('Riga', 'Warsaw'),
        ('Warsaw', 'Tallinn'), ('Tallinn', 'Warsaw'),
        ('Copenhagen', 'Helsinki'), ('Helsinki', 'Copenhagen'),
        ('Lyon', 'Paris'), ('Paris', 'Lyon'),
        ('Copenhagen', 'Warsaw'), ('Warsaw', 'Copenhagen'),
        ('Lyon', 'Oslo'), ('Oslo', 'Lyon'),
        ('Paris', 'Oslo'), ('Oslo', 'Paris'),
        ('Paris', 'Riga'), ('Riga', 'Paris'),
        ('Krakow', 'Helsinki'), ('Helsinki', 'Krakow'),
        ('Paris', 'Tallinn'), ('Tallinn', 'Paris'),
        ('Oslo', 'Riga'), ('Riga', 'Oslo'),
        ('Krakow', 'Warsaw'), ('Warsaw', 'Krakow'),
        ('Paris', 'Helsinki'), ('Helsinki', 'Paris'),
        ('Copenhagen', 'Santorini'), ('Santorini', 'Copenhagen'),
        ('Helsinki', 'Warsaw'), ('Warsaw', 'Helsinki'),
        ('Helsinki', 'Riga'), ('Riga', 'Helsinki'),
        ('Copenhagen', 'Krakow'), ('Krakow', 'Copenhagen'),
        ('Copenhagen', 'Riga'), ('Riga', 'Copenhagen'),
        ('Paris', 'Krakow'), ('Krakow', 'Paris'),
        ('Copenhagen', 'Oslo'), ('Oslo', 'Copenhagen'),
        ('Oslo', 'Tallinn'), ('Tallinn', 'Oslo'),
        ('Oslo', 'Helsinki'), ('Helsinki', 'Oslo'),
        ('Copenhagen', 'Tallinn'), ('Tallinn', 'Copenhagen'),
        ('Oslo', 'Krakow'), ('Krakow', 'Oslo'),
        ('Riga', 'Tallinn'), ('Tallinn', 'Riga'),
        ('Helsinki', 'Tallinn'), ('Tallinn', 'Helsinki'),
        ('Paris', 'Copenhagen'), ('Copenhagen', 'Paris'),
        ('Paris', 'Warsaw'), ('Warsaw', 'Paris'),
        ('Santorini', 'Oslo'), ('Oslo', 'Santorini'),
        ('Oslo', 'Warsaw'), ('Warsaw', 'Oslo'),
    }

    # Define the itinerary order
    itinerary_order = [
        'Lyon', 'Paris', 'Copenhagen', 'Santorini', 'Oslo', 'Krakow', 'Helsinki', 'Oslo', 'Riga'
    ]

    # Calculate the day ranges for each city in the itinerary
    itinerary = []
    current_day = 1
    for city in itinerary_order:
        duration = cities[city]['duration']
        start_day = current_day
        end_day = current_day + duration - 1
        # Check if the city has a constraint
        if cities[city]['constraint']:
            constraint_start, constraint_end = cities[city]['constraint']
            # Adjust the start and end days to meet the constraint
            start_day = constraint_start
            end_day = constraint_end
            current_day = end_day + 1
        else:
            current_day = end_day + 1
        itinerary.append({
            'city': city,
            'start_day': start_day,
            'end_day': end_day
        })

    # Check for direct flights between consecutive cities
    for i in range(len(itinerary) - 1):
        city1 = itinerary[i]['city']
        city2 = itinerary[i+1]['city']
        if (city1, city2) not in direct_flights:
            raise ValueError(f"No direct flight from {city1} to {city2}")

    # Convert to the required JSON format
    json_output = {'itinerary': []}
    for entry in itinerary:
        day_range = f"Day {entry['start_day']}-Day {entry['end_day']}"
        json_output['itinerary'].append({'day_range': day_range, 'place': entry['city']})

    print(json.dumps(json_output, indent=2))

if __name__ == '__main__':
    main()