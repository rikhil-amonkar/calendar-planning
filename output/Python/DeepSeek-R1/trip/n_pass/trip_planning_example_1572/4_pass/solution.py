import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Berlin"},
        {"day_range": "Day 3-6", "place": "Paris"},
        {"day_range": "Day 7-8", "place": "Lyon"},
        {"day_range": "Day 9-11", "place": "Nice"},
        {"day_range": "Day 12-14", "place": "Milan"},
        {"day_range": "Day 15-17", "place": "Rome"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()