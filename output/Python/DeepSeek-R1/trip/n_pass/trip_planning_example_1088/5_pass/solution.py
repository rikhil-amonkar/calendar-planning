import json

def main():
    itinerary = {
        "itinerary": [
            {"day_range": "Day 1-2", "place": "Reykjavik"},
            {"day_range": "Day 3-7", "place": "Oslo"},
            {"day_range": "Day 8-10", "place": "Stockholm"},
            {"day_range": "Day 11-12", "place": "Geneva"},
            {"day_range": "Day 13-15", "place": "Split"},
            {"day_range": "Day 16-20", "place": "Stuttgart"},
            {"day_range": "Day 21", "place": "Porto"},
            {"day_range": "Day 22-23", "place": "Reykjavik"}
        ]
    }
    print(json.dumps(itinerary))

if __name__ == "__main__":
    main()