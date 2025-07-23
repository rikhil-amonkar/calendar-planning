import json

def main():
    itinerary = [
        {"place": "Venice", "day_range": "Day 1-5"},
        {"place": "Edinburgh", "day_range": "Day 5-8"},
        {"place": "Krakow", "day_range": "Day 8-11"},
        {"place": "Stuttgart", "day_range": "Day 11-13"},
        {"place": "Split", "day_range": "Day 13-14"},
        {"place": "Athens", "day_range": "Day 14-17"},
        {"place": "Mykonos", "day_range": "Day 17-20"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()