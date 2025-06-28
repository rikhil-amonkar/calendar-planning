import json

def main():
    cities_order = ['Krakow', 'Frankfurt', 'Dubrovnik', 'Naples', 'Oslo']
    required = {
        'Krakow': 5,
        'Frankfurt': 3,
        'Dubrovnik': 4,
        'Naples': 4,
        'Oslo': 2
    }
    
    itinerary = []
    start = 1
    for city in cities_order:
        days = required[city]
        end = start + days - 1
        # Format day range based on duration
        if days == 1:
            day_range_str = f"Day {start}"
        else:
            day_range_str = f"Day {start}-{end}"
        
        itinerary.append({
            "day_range": day_range_str,
            "place": city
        })
        start = end + 1

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()