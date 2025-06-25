import json

def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Porto"},
        {"day_range": "Day 5-8", "place": "Amsterdam"},
        {"day_range": "Day 8-11", "place": "Helsinki"},
        {"day_range": "Day 11-15", "place": "Reykjavik"},
        {"day_range": "Day 15-17", "place": "Warsaw"},
        {"day_range": "Day 17-20", "place": "Naples"},
        {"day_range": "Day 20-22", "place": "Brussels"},
        {"day_range": "Day 22-23", "place": "Valencia"},
        {"day_range": "Day 23-25", "place": "Lyon"},
        {"day_range": "Day 25-27", "place": "Split"}
    ]
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()