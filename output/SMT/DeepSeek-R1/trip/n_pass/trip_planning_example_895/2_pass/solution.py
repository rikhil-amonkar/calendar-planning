import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Brussels"},
        {"day_range": "Day 2", "place": "Brussels"},
        {"day_range": "Day 2", "place": "Reykjavik"},
        {"day_range": "Day 2-5", "place": "Reykjavik"},
        {"day_range": "Day 5", "place": "Reykjavik"},
        {"day_range": "Day 5", "place": "Venice"},
        {"day_range": "Day 5-7", "place": "Venice"},
        {"day_range": "Day 7", "place": "Venice"},
        {"day_range": "Day 7", "place": "Madrid"},
        {"day_range": "Day 7-11", "place": "Madrid"},
        {"day_range": "Day 11", "place": "Madrid"},
        {"day_range": "Day 11", "place": "London"},
        {"day_range": "Day 11-14", "place": "London"},
        {"day_range": "Day 14", "place": "London"},
        {"day_range": "Day 14", "place": "Santorini"},
        {"day_range": "Day 14-17", "place": "Santorini"},
        {"day_range": "Day 17", "place": "Santorini"},
        {"day_range": "Day 17", "place": "Lisbon"},
        {"day_range": "Day 17", "place": "Lisbon"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()