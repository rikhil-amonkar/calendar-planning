import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Reykjavik"},
        {"day_range": "Day 2-4", "place": "Stockholm"},
        {"day_range": "Day 4-9", "place": "Oslo"},
        {"day_range": "Day 9-12", "place": "Split"},
        {"day_range": "Day 12-17", "place": "Stuttgart"},
        {"day_range": "Day 17-19", "place": "Geneva"},
        {"day_range": "Day 19-21", "place": "Porto"}
    ]
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()