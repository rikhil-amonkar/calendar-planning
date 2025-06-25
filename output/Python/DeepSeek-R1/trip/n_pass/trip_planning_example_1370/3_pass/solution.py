import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Vilnius"},
        {"day_range": "Day 3-7", "place": "Munich"},
        {"day_range": "Day 8-11", "place": "Amsterdam"},
        {"day_range": "Day 12-15", "place": "Paris"},
        {"day_range": "Day 16-17", "place": "Geneva"},
        {"day_range": "Day 18-21", "place": "Split"},
        {"day_range": "Day 22-26", "place": "Krakow"},
        {"day_range": "Day 27-30", "place": "Budapest"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()