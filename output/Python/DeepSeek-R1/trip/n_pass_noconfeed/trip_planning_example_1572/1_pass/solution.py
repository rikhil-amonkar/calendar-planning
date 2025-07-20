import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Berlin"},
        {"day_range": "Day 2-4", "place": "Riga"},
        {"day_range": "Day 4-7", "place": "Stockholm"},
        {"day_range": "Day 7-10", "place": "Berlin"},
        {"day_range": "Day 10-15", "place": "Zurich"},
        {"day_range": "Day 15-17", "place": "Milan"},
        {"day_range": "Day 17-20", "place": "Naples"},
        {"day_range": "Day 20-23", "place": "Stockholm"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()