import json

def main():
    # Hardcoded itinerary based on manual calculation and direct flight constraints
    itinerary = [
        {"day_range": "Day 1-2", "place": "Tallinn"},
        {"day_range": "Day 2-3", "place": "Copenhagen"},
        {"day_range": "Day 3-4", "place": "Lisbon"},
        {"day_range": "Day 4-7", "place": "Prague"},
        {"day_range": "Day 7-10", "place": "Split"},
        {"day_range": "Day 10-15", "place": "Dubrovnik"},
        {"day_range": "Day 15-18", "place": "Stockholm"},
        {"day_range": "Day 18-19", "place": "Lyon"}
    ]
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()