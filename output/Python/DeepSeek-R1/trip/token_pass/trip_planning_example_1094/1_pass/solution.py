import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Paris"},
        {"day_range": "Day 3", "place": "Paris -> Barcelona"},
        {"day_range": "Day 3-4", "place": "Barcelona"},
        {"day_range": "Day 5", "place": "Barcelona -> Vienna"},
        {"day_range": "Day 5-8", "place": "Vienna"},
        {"day_range": "Day 9", "place": "Vienna -> Krakow"},
        {"day_range": "Day 9-11", "place": "Krakow"},
        {"day_range": "Day 11", "place": "Krakow -> Hamburg"},
        {"day_range": "Day 11-12", "place": "Hamburg"},
        {"day_range": "Day 13", "place": "Hamburg -> Edinburgh"},
        {"day_range": "Day 13-16", "place": "Edinburgh"},
        {"day_range": "Day 16", "place": "Edinburgh -> Stockholm"}
    ]
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()