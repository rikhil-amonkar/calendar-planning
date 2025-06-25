import json

def main():
    itinerary = [
        {"day_range": "Day 1-3", "place": "Edinburgh"},
        {"day_range": "Day 4-6", "place": "Stuttgart"},
        {"day_range": "Day 7-9", "place": "Krakow"},
        {"day_range": "Day 10", "place": "Vienna"},
        {"day_range": "Day 11", "place": "Venice"},
        {"day_range": "Day 12", "place": "Zagreb"},
        {"day_range": "Day 13-14", "place": "Split"},
        {"day_range": "Day 15", "place": "Athens"},
        {"day_range": "Day 16-18", "place": "Mykonos"},
        {"day_range": "Day 19-20", "place": "Athens"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()