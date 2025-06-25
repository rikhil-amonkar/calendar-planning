import json

def main():
    print(json.dumps({
        "itinerary": [
            {"day_range": "Day 1-4", "place": "Warsaw"},
            {"day_range": "Day 5-6", "place": "Riga"},
            {"day_range": "Day 7-9", "place": "Oslo"},
            {"day_range": "Day 10-11", "place": "Dubrovnik"},
            {"day_range": "Day 12-13", "place": "Madrid"},
            {"day_range": "Day 14-16", "place": "London"},
            {"day_range": "Day 17-18", "place": "Reykjavik"}
        ]
    }))

if __name__ == "__main__":
    main()