import json

def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Edinburgh"},
        {"day_range": "Day 6-10", "place": "Barcelona"},
        {"day_range": "Day 11-15", "place": "Budapest"},
        {"day_range": "Day 16", "place": "Stockholm"},
        {"day_range": "Day 17-20", "place": "Munich"},
        {"day_range": "Day 21-25", "place": "Vienna"},
        {"day_range": "Day 26-30", "place": "Warsaw"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()