import json

def main():
    # Define direct flights as a set of tuples (city1, city2)
    direct_flights = {
        ('Valencia', 'Frankfurt'),
        ('Frankfurt', 'Valencia'),
        ('Vienna', 'Bucharest'),
        ('Bucharest', 'Vienna'),
        ('Valencia', 'Athens'),
        ('Athens', 'Valencia'),
        ('Athens', 'Bucharest'),
        ('Bucharest', 'Athens'),
        ('Riga', 'Frankfurt'),
        ('Frankfurt', 'Riga'),
        ('Stockholm', 'Athens'),
        ('Athens', 'Stockholm'),
        ('Amsterdam', 'Bucharest'),
        ('Bucharest', 'Amsterdam'),
        ('Athens', 'Riga'),
        ('Riga', 'Athens'),
        ('Amsterdam', 'Frankfurt'),
        ('Frankfurt', 'Amsterdam'),
        ('Stockholm', 'Vienna'),
        ('Vienna', 'Stockholm'),
        ('Vienna', 'Riga'),
        ('Riga', 'Vienna'),
        ('Amsterdam', 'Reykjavik'),
        ('Reykjavik', 'Amsterdam'),
        ('Reykjavik', 'Frankfurt'),
        ('Frankfurt', 'Reykjavik'),
        ('Stockholm', 'Amsterdam'),
        ('Amsterdam', 'Stockholm'),
        ('Amsterdam', 'Valencia'),
        ('Valencia', 'Amsterdam'),
        ('Vienna', 'Frankfurt'),
        ('Frankfurt', 'Vienna'),
        ('Valencia', 'Bucharest'),
        ('Bucharest', 'Valencia'),
        ('Bucharest', 'Frankfurt'),
        ('Frankfurt', 'Bucharest'),
        ('Stockholm', 'Frankfurt'),
        ('Frankfurt', 'Stockholm'),
        ('Valencia', 'Vienna'),
        ('Vienna', 'Valencia'),
        ('Reykjavik', 'Athens'),
        ('Athens', 'Reykjavik'),
        ('Frankfurt', 'Salzburg'),
        ('Salzburg', 'Frankfurt'),
        ('Amsterdam', 'Vienna'),
        ('Vienna', 'Amsterdam'),
        ('Stockholm', 'Riga'),
        ('Riga', 'Stockholm'),
        ('Amsterdam', 'Riga'),
        ('Riga', 'Amsterdam'),
        ('Stockholm', 'Riga'),
        ('Riga', 'Stockholm'),
        ('Vienna', 'Riga'),
        ('Riga', 'Vienna'),
        ('Amsterdam', 'Athens'),
        ('Athens', 'Amsterdam'),
        ('Athens', 'Frankfurt'),
        ('Frankfurt', 'Athens'),
        ('Vienna', 'Athens'),
        ('Athens', 'Vienna'),
        ('Riga', 'Bucharest'),
        ('Bucharest', 'Riga'),
        ('Stockholm', 'Reykjavik'),
        ('Reykjavik', 'Stockholm'),
        ('Amsterdam', 'Riga'),
        ('Riga', 'Amsterdam'),
        ('Stockholm', 'Reykjavik'),
        ('Reykjavik', 'Stockholm'),
        ('Vienna', 'Reykjavik'),
        ('Reykjavik', 'Vienna'),
        ('Amsterdam', 'Athens'),
        ('Athens', 'Amsterdam'),
        ('Athens', 'Frankfurt'),
        ('Frankfurt', 'Athens'),
        ('Vienna', 'Athens'),
        ('Athens', 'Vienna'),
        ('Riga', 'Bucharest'),
        ('Bucharest', 'Riga'),
    }

    # Define the itinerary as a list of cities with start and end days
    itinerary = [
        {"city": "Stockholm", "start": 1, "end": 3},
        {"city": "Amsterdam", "start": 3, "end": 5},
        {"city": "Valencia", "start": 5, "end": 6},
        {"city": "Bucharest", "start": 6, "end": 8},
        {"city": "Vienna", "start": 8, "end": 12},
        {"city": "Athens", "start": 12, "end": 16},
        {"city": "Riga", "start": 16, "end": 18},
        {"city": "Reykjavik", "start": 18, "end": 22},
        {"city": "Frankfurt", "start": 22, "end": 25},
        {"city": "Salzburg", "start": 25, "end": 29},
    ]

    # Validate transitions between cities
    for i in range(len(itinerary) - 1):
        current_city = itinerary[i]["city"]
        next_city = itinerary[i + 1]["city"]
        if (current_city, next_city) not in direct_flights:
            raise ValueError(f"No direct flight from {current_city} to {next_city}")

    # Convert the itinerary to the required JSON format
    result = {"itinerary": []}
    for entry in itinerary:
        start_day = entry["start"]
        end_day = entry["end"]
        day_range = f"Day {start_day}-{end_day}"
        result["itinerary"].append({"day_range": day_range, "place": entry["city"]})

    # Output the result as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()