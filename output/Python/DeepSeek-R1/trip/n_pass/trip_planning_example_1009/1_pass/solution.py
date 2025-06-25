import json

def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Manchester"},
        {"day_range": "Day 5-6", "place": "Vienna"},
        {"day_range": "Day 6-11", "place": "Stuttgart"},
        {"day_range": "Day 11-13", "place": "Istanbul"},
        {"day_range": "Day 13-16", "place": "Riga"},
        {"day_range": "Day 16-19", "place": "Bucharest"},
        {"day_range": "Day 19-20", "place": "Vienna"},
        {"day_range": "Day 20-23", "place": "Florence"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()