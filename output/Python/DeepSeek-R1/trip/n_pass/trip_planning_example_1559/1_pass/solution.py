import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Tallinn"},
        {"day_range": "Day 2-4", "place": "Prague"},
        {"day_range": "Day 4-5", "place": "Valencia"},
        {"day_range": "Day 5-9", "place": "Seville"},
        {"day_range": "Day 9-10", "place": "Lisbon"},
        {"day_range": "Day 10-13", "place": "Paris"},
        {"day_range": "Day 13-15", "place": "Oslo"},
        {"day_range": "Day 15-18", "place": "Lyon"},
        {"day_range": "Day 18-21", "place": "Nice"},
        {"day_range": "Day 21-25", "place": "Mykonos"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()