import json

def main():
    itinerary = [
        {"day_range": "Day 1", "place": "Brussels"},
        {"day_range": "Day 2", "place": "Brussels"},
        {"day_range": "Day 3", "place": "Brussels"},
        {"day_range": "Day 4", "place": "Naples"},
        {"day_range": "Day 5", "place": "Naples"},
        {"day_range": "Day 6", "place": "Naples"},
        {"day_range": "Day 7", "place": "Athens"},
        {"day_range": "Day 8", "place": "Athens"},
        {"day_range": "Day 9", "place": "Athens"},
        {"day_range": "Day 10", "place": "Copenhagen"},
        {"day_range": "Day 11", "place": "Copenhagen"},
        {"day_range": "Day 12", "place": "Copenhagen"},
        {"day_range": "Day 13", "place": "Copenhagen"},
        {"day_range": "Day 14", "place": "Prague"},
        {"day_range": "Day 15", "place": "Paris"},
        {"day_range": "Day 16", "place": "Paris"},
        {"day_range": "Day 17", "place": "Paris"},
        {"day_range": "Day 18", "place": "Paris"},
        {"day_range": "Day 19", "place": "Geneva"},
        {"day_range": "Day 20", "place": "Geneva"},
        {"day_range": "Day 21", "place": "Dubrovnik"},
        {"day_range": "Day 22", "place": "Dubrovnik"},
        {"day_range": "Day 23", "place": "Santorini"},
        {"day_range": "Day 24", "place": "Santorini"},
        {"day_range": "Day 25", "place": "Santorini"},
        {"day_range": "Day 26", "place": "Mykonos"},
        {"day_range": "Day 27", "place": "Mykonos"},
        {"day_range": "Day 28", "place": "Mykonos"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()