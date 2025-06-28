import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Edinburgh"},
        {"day_range": "Day 3-4", "place": "London"},
        {"day_range": "Day 5-6", "place": "Paris"},
        {"day_range": "Day 7-8", "place": "Zurich"},
        {"day_range": "Day 9-10", "place": "Milan"},
        {"day_range": "Day 11-12", "place": "Venice"},
        {"day_range": "Day 13-14", "place": "Nice"},
        {"day_range": "Day 15-16", "place": "Barcelona"}
    ]
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()