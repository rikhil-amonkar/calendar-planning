import json

def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Edinburgh"},
        {"day_range": "Day 6-10", "place": "Barcelona"},
        {"day_range": "Day 11-16", "place": "Budapest"},
        {"day_range": "Day 17", "place": "Stockholm"},
        {"day_range": "Day 18-21", "place": "Munich"},
        {"day_range": "Day 22-27", "place": "Vienna"},
        {"day_range": "Day 28-32", "place": "Warsaw"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()