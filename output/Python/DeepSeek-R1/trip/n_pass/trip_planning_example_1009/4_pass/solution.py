import json

def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Manchester"},
        {"day_range": "Day 6-10", "place": "Florence"},
        {"day_range": "Day 11-11", "place": "Vienna"},
        {"day_range": "Day 12-13", "place": "Istanbul"},
        {"day_range": "Day 14-19", "place": "Stuttgart"},
        {"day_range": "Day 20-22", "place": "Riga"},
        {"day_range": "Day 23-23", "place": "Bucharest"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()