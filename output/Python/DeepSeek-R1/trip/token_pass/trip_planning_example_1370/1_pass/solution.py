import json

def main():
    itinerary = [
        {"day_range": "Day 1-3", "place": "Vilnius"},
        {"day_range": "Day 4-8", "place": "Munich"},
        {"day_range": "Day 9-13", "place": "Paris"},
        {"day_range": "Day 14-17", "place": "Amsterdam"},
        {"day_range": "Day 18-22", "place": "Krakow"},
        {"day_range": "Day 23-24", "place": "Geneva"},
        {"day_range": "Day 25-29", "place": "Santorini"},
        {"day_range": "Day 30", "place": "Split"}
    ]
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()