import json

def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Reykjavik"},
        {"day_range": "Day 5-6", "place": "Oslo"},
        {"day_range": "Day 6-9", "place": "Istanbul"},
        {"day_range": "Day 9-10", "place": "Oslo"},
        {"day_range": "Day 10-14", "place": "Edinburgh"},
        {"day_range": "Day 14-16", "place": "Stuttgart"},
        {"day_range": "Day 16-19", "place": "Bucharest"}
    ]
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()