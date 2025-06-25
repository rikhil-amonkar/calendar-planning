import json

def main():
    itinerary = [
        {"day_range": "Day 1-3", "place": "Vilnius"},
        {"day_range": "Day 4-8", "place": "Munich"},
        {"day_range": "Day 9-12", "place": "Amsterdam"},
        {"day_range": "Day 13-16", "place": "Paris"},
        {"day_range": "Day 17-21", "place": "Split"},
        {"day_range": "Day 22-26", "place": "Krakow"},
        {"day_range": "Day 27-30", "place": "Budapest"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()