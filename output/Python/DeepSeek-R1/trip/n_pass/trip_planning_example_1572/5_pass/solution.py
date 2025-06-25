import json

def main():
    itinerary = [
        {"day_range": "Day 1-3", "place": "Berlin"},
        {"day_range": "Day 4-8", "place": "Paris"},
        {"day_range": "Day 9-11", "place": "Lyon"},
        {"day_range": "Day 12-15", "place": "Nice"},
        {"day_range": "Day 16-19", "place": "Milan"},
        {"day_range": "Day 20-23", "place": "Rome"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()