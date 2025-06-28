import json

def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Vienna"},
        {"day_range": "Day 5-9", "place": "Prague"},
        {"day_range": "Day 9-12", "place": "Split"},
        {"day_range": "Day 12-14", "place": "Amsterdam"},
        {"day_range": "Day 14-16", "place": "Brussels"},
        {"day_range": "Day 16-17", "place": "Riga"},
        {"day_range": "Day 17-18", "place": "Stockholm"},
        {"day_range": "Day 18-20", "place": "Istanbul"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()