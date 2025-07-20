import json

def main():
    itinerary = [
        {"day_range": "Day 1-3", "place": "Berlin"},
        {"day_range": "Day 3-4", "place": "Barcelona"},
        {"day_range": "Day 4-5", "place": "Lyon"},
        {"day_range": "Day 6-10", "place": "Nice"},
        {"day_range": "Day 10-14", "place": "Athens"},
        {"day_range": "Day 14-17", "place": "Vilnius"},
        {"day_range": "Day 17-20", "place": "Berlin"}
    ]
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()