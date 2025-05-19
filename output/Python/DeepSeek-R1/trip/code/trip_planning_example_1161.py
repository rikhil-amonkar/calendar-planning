import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Oslo"},
        {"day_range": "Day 2-4", "place": "Dubrovnik"},
        {"day_range": "Day 5-6", "place": "Helsinki"},
        {"day_range": "Day 6-7", "place": "Vilnius"},
        {"day_range": "Day 7-8", "place": "Paris"},
        {"day_range": "Day 8-12", "place": "Krakow"},
        {"day_range": "Day 12-16", "place": "Madrid"},
        {"day_range": "Day 16-18", "place": "Mykonos"}
    ]
    
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()