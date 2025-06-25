import json

def main():
    itinerary = [
        {"day_range": "1-2", "place": "Frankfurt"},
        {"day_range": "3-4", "place": "Venice"},
        {"day_range": "5-6", "place": "Rome"},
        {"day_range": "7-8", "place": "Nice"},
        {"day_range": "9-10", "place": "Mykonos"},
        {"day_range": "11-12", "place": "Seville"},
        {"day_range": "13-14", "place": "Stuttgart"},
        {"day_range": "15-16", "place": "Dublin"},
        {"day_range": "17-18", "place": "Lisbon"},
        {"day_range": "19-20", "place": "Bucharest"},
        {"day_range": "21-22", "place": "Frankfurt"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()