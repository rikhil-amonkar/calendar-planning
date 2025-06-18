import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Oslo"},
        {"day_range": "Day 2", "place": "Oslo"},
        {"day_range": "Day 2", "place": "Dubrovnik"},
        {"day_range": "Day 2-4", "place": "Dubrovnik"},
        {"day_range": "Day 4", "place": "Dubrovnik"},
        {"day_range": "Day 4", "place": "Helsinki"},
        {"day_range": "Day 4-5", "place": "Helsinki"},
        {"day_range": "Day 5", "place": "Helsinki"},
        {"day_range": "Day 5", "place": "Krakow"},
        {"day_range": "Day 5-9", "place": "Krakow"},
        {"day_range": "Day 9", "place": "Krakow"},
        {"day_range": "Day 9", "place": "Vilnius"},
        {"day_range": "Day 9-10", "place": "Vilnius"},
        {"day_range": "Day 10", "place": "Vilnius"},
        {"day_range": "Day 10", "place": "Paris"},
        {"day_range": "Day 10-11", "place": "Paris"},
        {"day_range": "Day 11", "place": "Paris"},
        {"day_range": "Day 11", "place": "Madrid"},
        {"day_range": "Day 11-15", "place": "Madrid"},
        {"day_range": "Day 15", "place": "Madrid"},
        {"day_range": "Day 15", "place": "Mykonos"},
        {"day_range": "Day 15-18", "place": "Mykonos"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()