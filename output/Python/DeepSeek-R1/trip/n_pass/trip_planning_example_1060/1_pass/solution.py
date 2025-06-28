import json

def main():
    itinerary = [
        {"day_range": "Day 1-4", "place": "Reykjavik"},
        {"day_range": "Day 4-7", "place": "Stuttgart"},
        {"day_range": "Day 7-11", "place": "Valencia"},
        {"day_range": "Day 11-13", "place": "Seville"},
        {"day_range": "Day 13-15", "place": "Munich"},
        {"day_range": "Day 15-19", "place": "Geneva"},
        {"day_range": "Day 19-22", "place": "Istanbul"},
        {"day_range": "Day 22-25", "place": "Vilnius"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()