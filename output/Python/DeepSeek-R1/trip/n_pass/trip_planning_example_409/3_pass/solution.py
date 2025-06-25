import json

def main():
    itinerary = [
        {"day_range": "Day 1", "place": "Helsinki"},
        {"day_range": "Day 2 to Day 3", "place": "Zurich"},
        {"day_range": "Day 4 to Day 8", "place": "Split"},
        {"day_range": "Day 9", "place": "Split"},
        {"day_range": "Day 10", "place": "Hamburg"},
        {"day_range": "Day 11 to Day 12", "place": "Helsinki"}
    ]
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()