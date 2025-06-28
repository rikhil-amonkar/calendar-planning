import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Paris"},
        {"day_range": "Day 2-4", "place": "Krakow"},
        {"day_range": "Day 4-7", "place": "Vienna"},
        {"day_range": "Day 7-10", "place": "Riga"},
        {"day_range": "Day 10-11", "place": "Hamburg"},
        {"day_range": "Day 11-14", "place": "Edinburgh"},
        {"day_range": "Day 14-15", "place": "Barcelona"},
        {"day_range": "Day 15-16", "place": "Stockholm"}
    ]
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()