import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Berlin"},
        {"day_range": "Day 2-7", "place": "Paris"},
        {"day_range": "Day 7-10", "place": "Lyon"},
        {"day_range": "Day 10-13", "place": "Nice"},
        {"day_range": "Day 13-17", "place": "Zurich"},
        {"day_range": "Day 17-20", "place": "Milan"},
        {"day_range": "Day 20-23", "place": "Naples"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()