import json

def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Manchester"},
        {"day_range": "Day 5-9", "place": "Florence"},
        {"day_range": "Day 9-10", "place": "Vienna"},
        {"day_range": "Day 10-12", "place": "Istanbul"},
        {"day_range": "Day 12-17", "place": "Stuttgart"},
        {"day_range": "Day 17-20", "place": "Riga"},
        {"day_range": "Day 20-23", "place": "Bucharest"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()