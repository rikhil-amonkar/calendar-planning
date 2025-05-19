import json

def main():
    city_days = {
        'Porto': 5,
        'Prague': 4,
        'Reykjavik': 4,
        'Santorini': 2,
        'Amsterdam': 2,
        'Munich': 4
    }
    
    flight_graph = {
        'Porto': ['Amsterdam', 'Munich'],
        'Amsterdam': ['Porto', 'Munich', 'Reykjavik', 'Santorini', 'Prague'],
        'Munich': ['Amsterdam', 'Porto', 'Reykjavik', 'Prague'],
        'Reykjavik': ['Amsterdam', 'Prague', 'Munich'],
        'Prague': ['Reykjavik', 'Amsterdam', 'Munich'],
        'Santorini': ['Amsterdam']
    }

    itinerary = [
        ('Prague', 1, 4),
        ('Reykjavik', 4, 7),
        ('Munich', 7, 10),
        ('Porto', 10, 14),
        ('Amsterdam', 14, 15),
        ('Santorini', 15, 16)
    ]

    # Validate day counts
    for city, start, end in itinerary:
        assert end - start + 1 == city_days[city], f"Day count mismatch for {city}"

    # Validate transitions
    for i in range(1, len(itinerary)):
        prev_city = itinerary[i-1][0]
        current_city = itinerary[i][0]
        if current_city not in flight_graph[prev_city]:
            raise ValueError(f"No direct flight from {prev_city} to {current_city}")

    # Format output
    formatted = []
    for entry in itinerary:
        start, end = entry[1], entry[2]
        day_range = f"Day {start}-{end}" if start != end else f"Day {start}"
        formatted.append({"day_range": day_range, "place": entry[0]})

    print(json.dumps({"itinerary": formatted}, indent=2))

if __name__ == "__main__":
    main()