import json

def main():
    itinerary = [
        {"day_range": "Day 1", "place": "Tallinn"},
        {"day_range": "Day 2-4", "place": "Prague"},
        {"day_range": "Day 5", "place": "Valencia"},
        {"day_range": "Day 6-9", "place": "Seville"},
        {"day_range": "Day 10", "place": "Lisbon"},
        {"day_range": "Day 11-13", "place": "Paris"},
        {"day_range": "Day 14-15", "place": "Oslo"},
        {"day_range": "Day 16-17", "place": "Lyon"},
        {"day_range": "Day 18-21", "place": "Nice"},
        {"day_range": "Day 22-25", "place": "Mykonos"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()