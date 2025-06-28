import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Paris"},
        {"day_range": "Day 3-4", "place": "Krakow"},
        {"day_range": "Day 5-6", "place": "Vienna"},
        {"day_range": "Day 7-8", "place": "Riga"},
        {"day_range": "Day 9-10", "place": "Hamburg"},
        {"day_range": "Day 11-12", "place": "Edinburgh"},
        {"day_range": "Day 13-14", "place": "Barcelona"},
        {"day_range": "Day 15-16", "place": "Stockholm"}
    ]
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()