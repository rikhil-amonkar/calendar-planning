import json

def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Prague"},
        {"day_range": "Day 5-8", "place": "Riga"},
        {"day_range": "Day 8-10", "place": "Stockholm"},
        {"day_range": "Day 10-15", "place": "Santorini"},
        {"day_range": "Day 15-20", "place": "Naples"},
        {"day_range": "Day 20-22", "place": "Warsaw"},
        {"day_range": "Day 22-25", "place": "Tallinn"},
        {"day_range": "Day 25-28", "place": "Milan"}
    ]
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()