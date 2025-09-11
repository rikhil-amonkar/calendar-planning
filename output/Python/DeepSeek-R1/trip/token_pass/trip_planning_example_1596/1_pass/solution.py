import json

def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Edinburgh"},
        {"day_range": "Day 5-9", "place": "Barcelona"},
        {"day_range": "Day 9-13", "place": "Budapest"},
        {"day_range": "Day 14-18", "place": "Riga"},
        {"day_range": "Day 18-20", "place": "Munich"},
        {"day_range": "Day 21-25", "place": "Vienna"},
        {"day_range": "Day 25-29", "place": "Warsaw"},
        {"day_range": "Day 29-32", "place": "Krakow"}
    ]
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()