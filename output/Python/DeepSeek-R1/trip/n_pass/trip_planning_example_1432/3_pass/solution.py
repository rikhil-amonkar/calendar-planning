import json

def main():
    itinerary = [
        {"day_range": "Day 1-3", "place": "Stockholm"},
        {"day_range": "Day 4-6", "place": "Amsterdam"},
        {"day_range": "Day 7-8", "place": "Valencia"},
        {"day_range": "Day 9-12", "place": "Vienna"},
        {"day_range": "Day 13-15", "place": "Frankfurt"},
        {"day_range": "Day 16-18", "place": "Athens"},
        {"day_range": "Day 19-20", "place": "Riga"},
        {"day_range": "Day 21-23", "place": "Bucharest"},
        {"day_range": "Day 24-26", "place": "Reykjavik"},
        {"day_range": "Day 27-29", "place": "Salzburg"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()