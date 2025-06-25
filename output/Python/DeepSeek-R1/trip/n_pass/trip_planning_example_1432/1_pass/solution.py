import json

def main():
    itinerary = [
        {"day_range": "Day 1-3", "place": "Stockholm"},
        {"day_range": "Day 3-5", "place": "Amsterdam"},
        {"day_range": "Day 5-6", "place": "Valencia"},
        {"day_range": "Day 6-10", "place": "Vienna"},
        {"day_range": "Day 10-13", "place": "Frankfurt"},
        {"day_range": "Day 14-18", "place": "Athens"},
        {"day_range": "Day 18-20", "place": "Riga"},
        {"day_range": "Day 20-23", "place": "Bucharest"},
        {"day_range": "Day 23-27", "place": "Reykjavik"},
        {"day_range": "Day 27-29", "place": "Salzburg"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()