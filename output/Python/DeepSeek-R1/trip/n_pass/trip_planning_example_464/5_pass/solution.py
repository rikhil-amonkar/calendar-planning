import json

def main():
    cities_order = ['Krakow', 'Frankfurt', 'Dubrovnik', 'Naples', 'Oslo']
    # Adjusted days: reduced Krakow by 1, Dubrovnik by 1 to meet 16-day limit
    required = {
        'Krakow': 4,    # Minimum is 3
        'Frankfurt': 3,  # Minimum is 2
        'Dubrovnik': 3,  # Minimum is 3
        'Naples': 4,     # Minimum is 3
        'Oslo': 2        # Minimum is 2
    }
    
    itinerary = []
    start = 1
    for city in cities_order:
        days = required[city]
        end = start + days - 1
        day_range_str = f"Day {start}-{end}" if days > 1 else f"Day {start}"
        itinerary.append({
            "day_range": day_range_str,
            "place": city
        })
        start = end + 1

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()