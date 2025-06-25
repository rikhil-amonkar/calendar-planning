import json

def main():
    itinerary = [
        {"day_range": "1-6", "place": "Frankfurt"},
        {"day_range": "6-9", "place": "Venice"},
        {"day_range": "9-11", "place": "Rome"},
        {"day_range": "11-13", "place": "Nice"},
        {"day_range": "13-14", "place": "Mykonos"},
        {"day_range": "14-18", "place": "Seville"},
        {"day_range": "18-21", "place": "Stuttgart"},
        {"day_range": "21-22", "place": "Dublin"},
        {"day_range": "22-23", "place": "Lisbon"},
        {"day_range": "23-24", "place": "Bucharest"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()