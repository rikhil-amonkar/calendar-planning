import json

def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Vienna"},
        {"day_range": "Day 5-9", "place": "Prague"},
        {"day_range": "Day 9-10", "place": "Munich"},
        {"day_range": "Day 11-13", "place": "Split"},
        {"day_range": "Day 14-15", "place": "Istanbul"},
        {"day_range": "Day 15-16", "place": "Riga"},
        {"day_range": "Day 16-17", "place": "Stockholm"},
        {"day_range": "Day 18-19", "place": "Amsterdam"},
        {"day_range": "Day 20", "place": "Brussels"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()