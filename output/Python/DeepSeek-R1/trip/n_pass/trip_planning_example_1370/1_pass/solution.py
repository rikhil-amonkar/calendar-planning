import json

def main():
    itinerary = [
        {"day_range": "Day 1-3", "place": "Vilnius"},
        {"day_range": "Day 3-8", "place": "Munich"},
        {"day_range": "Day 8-12", "place": "Amsterdam"},
        {"day_range": "Day 12-16", "place": "Paris"},
        {"day_range": "Day 16-18", "place": "Geneva"},
        {"day_range": "Day 18-22", "place": "Split"},
        {"day_range": "Day 22-27", "place": "Krakow"},
        {"day_range": "Day 27-30", "place": "Budapest"},
        {"day_range": "Day 30", "place": "Santorini"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()