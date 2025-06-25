import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Tallinn"},
        {"day_range": "Day 3-5", "place": "Prague"},
        {"day_range": "Day 6-7", "place": "Valencia"},
        {"day_range": "Day 8-10", "place": "Seville"},
        {"day_range": "Day 11-12", "place": "Lisbon"},
        {"day_range": "Day 13-15", "place": "Paris"},
        {"day_range": "Day 16-17", "place": "Oslo"},
        {"day_range": "Day 18-19", "place": "Lyon"},
        {"day_range": "Day 20-22", "place": "Nice"},
        {"day_range": "Day 23-25", "place": "Mykonos"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()