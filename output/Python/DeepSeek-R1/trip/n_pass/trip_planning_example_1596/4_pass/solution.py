import json

def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Edinburgh"},
        {"day_range": "Day 6-10", "place": "Barcelona"},
        {"day_range": "Day 11-15", "place": "Budapest"},
        {"day_range": "Day 16-18", "place": "Stockholm"},  # Extended to 3 days
        {"day_range": "Day 19-22", "place": "Munich"},
        {"day_range": "Day 23-27", "place": "Vienna"},
        {"day_range": "Day 28-32", "place": "Warsaw"}      # Extended to cover 32 days
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()