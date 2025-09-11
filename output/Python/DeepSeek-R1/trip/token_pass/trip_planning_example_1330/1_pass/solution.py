import json

def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Zurich"},
        {"day_range": "Day 5-9", "place": "Venice"},
        {"day_range": "Day 9-11", "place": "Nice"},
        {"day_range": "Day 12-15", "place": "Hamburg"},
        {"day_range": "Day 16-17", "place": "Salzburg"},
        {"day_range": "Day 18-21", "place": "Copenhagen"},
        {"day_range": "Day 21-22", "place": "Brussels"},
        {"day_range": "Day 22-25", "place": "Naples"}
    ]
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()