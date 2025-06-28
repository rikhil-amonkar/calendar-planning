import json

def main():
    itinerary = [
        {"day_range": "Day 1-3", "place": "Vilnius"},
        {"day_range": "Day 4-8", "place": "Krakow"},
        {"day_range": "Day 9-12", "place": "Budapest"},
        {"day_range": "Day 13-17", "place": "Split"},
        {"day_range": "Day 18-22", "place": "Munich"},
        {"day_range": "Day 23-26", "place": "Amsterdam"},
        {"day_range": "Day 27-30", "place": "Paris"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()