import json

def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Edinburgh"},
        {"day_range": "Day 6", "place": "Barcelona"},
        {"day_range": "Day 7-10", "place": "Barcelona"},
        {"day_range": "Day 11", "place": "Budapest"},
        {"day_range": "Day 12-16", "place": "Budapest"},
        {"day_range": "Day 17", "place": "Stockholm"},
        {"day_range": "Day 18", "place": "Munich"},
        {"day_range": "Day 19-21", "place": "Munich"},
        {"day_range": "Day 22", "place": "Vienna"},
        {"day_range": "Day 23-27", "place": "Vienna"},
        {"day_range": "Day 28", "place": "Warsaw"},
        {"day_range": "Day 29-32", "place": "Warsaw"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()