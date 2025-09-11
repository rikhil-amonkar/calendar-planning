import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Paris"},
        {"day_range": "Day 2-6", "place": "Barcelona"},
        {"day_range": "Day 6-7", "place": "Amsterdam"},
        {"day_range": "Day 7-8", "place": "Tallinn"},
        {"day_range": "Day 8-11", "place": "Vilnius"},
        {"day_range": "Day 11-15", "place": "Warsaw"},
        {"day_range": "Day 15-18", "place": "Venice"},
        {"day_range": "Day 18-19", "place": "Florence"},
        {"day_range": "Day 19-22", "place": "Hamburg"},
        {"day_range": "Day 22-25", "place": "Salzburg"}
    ]
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()