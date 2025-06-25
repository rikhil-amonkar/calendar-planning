import json

def main():
    itinerary = [
        {"day_range": "Day 1-3", "place": "Santorini"},
        {"day_range": "Day 3-6", "place": "Vienna"},
        {"day_range": "Day 6-7", "place": "Madrid"},
        {"day_range": "Day 7-8", "place": "Seville"},
        {"day_range": "Day 8-11", "place": "Valencia"},
        {"day_range": "Day 11-15", "place": "Krakow"},
        {"day_range": "Day 15-18", "place": "Frankfurt"},
        {"day_range": "Day 18-20", "place": "Bucharest"},
        {"day_range": "Day 20-23", "place": "Riga"},
        {"day_range": "Day 23-27", "place": "Tallinn"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()