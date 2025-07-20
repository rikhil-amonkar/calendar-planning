import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Paris"},
        {"day_range": "Day 2-6", "place": "Vienna"},
        {"day_range": "Day 6-8", "place": "Barcelona"},
        {"day_range": "Day 8-12", "place": "Riga"},
        {"day_range": "Day 12-14", "place": "Krakow"},
        {"day_range": "Day 14-16", "place": "Hamburg"},
        {"day_range": "Day 16", "place": "Edinburgh"},
        {"day_range": "Day 16", "place": "Stockholm"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()