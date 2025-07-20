import json

def main():
    itinerary = [
        {"day_range": "Day 1-4", "place": "Florence"},
        {"day_range": "Day 4-5", "place": "Vienna"},
        {"day_range": "Day 5-8", "place": "Reykjavik"},
        {"day_range": "Day 8-12", "place": "Stuttgart"},
        {"day_range": "Day 12-13", "place": "Istanbul"},
        {"day_range": "Day 13-16", "place": "Riga"},
        {"day_range": "Day 16-19", "place": "Bucharest"},
        {"day_range": "Day 19-23", "place": "Manchester"}
    ]
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()