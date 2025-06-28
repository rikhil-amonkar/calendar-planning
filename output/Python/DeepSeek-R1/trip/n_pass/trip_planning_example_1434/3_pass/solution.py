import json

def main():
    itinerary = [
        {"day_range": "1-5", "place": "Frankfurt"},
        {"day_range": "5-8", "place": "Venice"},
        {"day_range": "8-10", "place": "Rome"},
        {"day_range": "10-12", "place": "Nice"},
        {"day_range": "12-13", "place": "Mykonos"},
        {"day_range": "13-17", "place": "Seville"},
        {"day_range": "17-20", "place": "Stuttgart"},
        {"day_range": "20-21", "place": "Dublin"},
        {"day_range": "21-22", "place": "Lisbon"},
        {"day_range": "22-23", "place": "Bucharest"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()