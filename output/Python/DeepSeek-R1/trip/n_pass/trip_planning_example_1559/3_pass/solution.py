import json

def main():
    itinerary = [
        {"day_range": "Day 1", "place": "Tallinn"},
        {"day_range": "Day 2-3", "place": "Prague"},
        {"day_range": "Day 4", "place": "Valencia"},
        {"day_range": "Day 5-7", "place": "Seville"},
        {"day_range": "Day 8", "place": "Lisbon"},
        {"day_range": "Day 9-10", "place": "Paris"},
        {"day_range": "Day 11-12", "place": "Oslo"},
        {"day_range": "Day 13-14", "place": "Lyon"},
        {"day_range": "Day 15-17", "place": "Nice"},
        {"day_range": "Day 18-20", "place": "Mykonos"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()