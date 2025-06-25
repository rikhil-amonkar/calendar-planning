import json

def main():
    itinerary = [
        {"day_range": "Day 1-4", "place": "Edinburgh"},   # 4 days
        {"day_range": "Day 5-9", "place": "Barcelona"},    # 5 days
        {"day_range": "Day 10-14", "place": "Budapest"},   # 5 days
        {"day_range": "Day 15-18", "place": "Stockholm"},  # 4 days
        {"day_range": "Day 19-22", "place": "Munich"},     # 4 days
        {"day_range": "Day 23-27", "place": "Vienna"},     # 5 days
        {"day_range": "Day 28-32", "place": "Warsaw"}      # 5 days
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()