import json

def main():
    itinerary = [
        {"day_range": "Day 1-4", "place": "Manchester"},
        {"day_range": "Day 5-8", "place": "Florence"},
        {"day_range": "Day 9-9", "place": "Vienna"},
        {"day_range": "Day 10-11", "place": "Istanbul"},
        {"day_range": "Day 12-16", "place": "Stuttgart"},
        {"day_range": "Day 17-19", "place": "Riga"},
        {"day_range": "Day 20-20", "place": "Bucharest"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()