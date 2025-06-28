import json

def main():
    itinerary = [
        {"day_range": "Day 1-3", "place": "Edinburgh"},
        {"day_range": "Day 4-7", "place": "Venice"},
        {"day_range": "Day 8-10", "place": "Stuttgart"},
        {"day_range": "Day 11-13", "place": "Krakow"},
        {"day_range": "Day 14-15", "place": "Split"},
        {"day_range": "Day 16-17", "place": "Mykonos"},
        {"day_range": "Day 18-20", "place": "Athens"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()