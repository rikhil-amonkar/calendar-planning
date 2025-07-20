import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Prague"},
        {"day_range": "Day 2", "place": "Prague"},
        {"day_range": "Day 2", "place": "Helsinki"},
        {"day_range": "Day 2-5", "place": "Helsinki"},
        {"day_range": "Day 5", "place": "Helsinki"},
        {"day_range": "Day 5", "place": "Naples"},
        {"day_range": "Day 5-8", "place": "Naples"},
        {"day_range": "Day 8", "place": "Naples"},
        {"day_range": "Day 8", "place": "Frankfurt"},
        {"day_range": "Day 8-10", "place": "Frankfurt"},
        {"day_range": "Day 10", "place": "Frankfurt"},
        {"day_range": "Day 10", "place": "Lyon"},
        {"day_range": "Day 10-12", "place": "Lyon"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()