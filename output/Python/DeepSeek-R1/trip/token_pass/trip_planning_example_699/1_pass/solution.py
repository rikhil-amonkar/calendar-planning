import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Hamburg"},
        {"day_range": "Day 2-6", "place": "Dublin"},
        {"day_range": "Day 6-9", "place": "London"},
        {"day_range": "Day 9-10", "place": "Reykjavik"},
        {"day_range": "Day 10-14", "place": "Helsinki"},
        {"day_range": "Day 14-16", "place": "Mykonos"}
    ]
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()