import json

def main():
    itinerary = [
        {"day_range": "Day 1-4", "place": "Prague"},
        {"day_range": "Day 5-8", "place": "Edinburgh"},
        {"day_range": "Day 9-10", "place": "Manchester"},
        {"day_range": "Day 11-15", "place": "Stuttgart"},
        {"day_range": "Day 16-20", "place": "Reykjavik"},
        {"day_range": "Day 21-25", "place": "Split"}
    ]
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()