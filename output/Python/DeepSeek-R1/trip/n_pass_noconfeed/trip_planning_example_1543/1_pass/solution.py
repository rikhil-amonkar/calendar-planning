import json

def main():
    itinerary_data = [
        {"start": 1, "end": 3, "place": "Prague"},
        {"start": 3, "end": 5, "place": "London"},
        {"start": 5, "end": 9, "place": "Lisbon"},
        {"start": 9, "end": 11, "place": "Athens"},
        {"start": 11, "end": 13, "place": "Dubrovnik"},
        {"start": 13, "end": 15, "place": "Dublin"},
        {"start": 15, "end": 16, "place": "Seville"},
        {"start": 16, "end": 20, "place": "Porto"},
        {"start": 20, "end": 23, "place": "Warsaw"},
        {"start": 23, "end": 26, "place": "Vilnius"}
    ]
    
    formatted_itinerary = []
    for stay in itinerary_data:
        day_range_str = f"Day {stay['start']}-{stay['end']}"
        formatted_itinerary.append({
            "day_range": day_range_str,
            "place": stay['place']
        })
    
    result = {"itinerary": formatted_itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()