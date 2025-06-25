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
    for i, city in enumerate(cities_order):
        days = required[city]
        end = start + days - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
        start = end + 1

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()