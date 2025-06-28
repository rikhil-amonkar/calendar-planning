import json

def main():
    itinerary = [
        {"day_range": "Day 1-4", "place": "Vienna"},
        {"day_range": "Day 5-7", "place": "Prague"},
        {"day_range": "Day 8-10", "place": "Split"},
        {"day_range": "Day 11-12", "place": "Amsterdam"},
        {"day_range": "Day 13-14", "place": "Brussels"},
        {"day_range": "Day 15-16", "place": "Riga"},
        {"day_range": "Day 17-18", "place": "Stockholm"},
        {"day_range": "Day 19-20", "place": "Istanbul"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()