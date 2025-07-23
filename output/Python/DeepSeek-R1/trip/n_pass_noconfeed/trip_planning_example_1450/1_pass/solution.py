import json

def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Oslo"},
        {"day_range": "Day 5-9", "place": "Krakow"},
        {"day_range": "Day 9-14", "place": "Vilnius"},
        {"day_range": "Day 14-19", "place": "Munich"},
        {"day_range": "Day 19-22", "place": "Stockholm"},
        {"day_range": "Day 22-24", "place": "Santorini"},
        {"day_range": "Day 24-29", "place": "Hamburg"},
        {"day_range": "Day 29", "place": "Hamburg and Istanbul"},
        {"day_range": "Day 25-29", "place": "Istanbul"},
        {"day_range": "Day 29-32", "place": "Frankfurt"}
    ]
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()