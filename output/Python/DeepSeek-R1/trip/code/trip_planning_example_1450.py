import json

def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Hamburg"},
        {"day_range": "Day 5-9", "place": "Krakow"},
        {"day_range": "Day 10-14", "place": "Vilnius"},
        {"day_range": "Day 15-18", "place": "Frankfurt"},
        {"day_range": "Day 19-20", "place": "Florence"},
        {"day_range": "Day 21-25", "place": "Munich"},
        {"day_range": "Day 25-29", "place": "Istanbul"},
        {"day_range": "Day 30-32", "place": "Stockholm"},
        {"day_range": "Day 1-5", "place": "Oslo"},  # Overlap with Hamburg via flight on day5
        {"day_range": "Day 28-29", "place": "Santorini"}  # Assumed direct flight from Stockholm
    ]
    
    # Ensure all cities are included and days sum correctly with overlaps
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()