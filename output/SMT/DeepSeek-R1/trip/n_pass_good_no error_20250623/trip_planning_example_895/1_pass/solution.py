import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Brussels"},
        {"day_range": "Day 2", "place": "Brussels"},  # Flight day (departure)
        {"day_range": "Day 2", "place": "Reykjavik"}, # Flight day (arrival)
        {"day_range": "Day 2-3", "place": "Reykjavik"},
        {"day_range": "Day 3", "place": "Reykjavik"}, # Flight day (departure)
        {"day_range": "Day 3", "place": "Venice"},    # Flight day (arrival)
        {"day_range": "Day 3-6", "place": "Venice"},
        {"day_range": "Day 6", "place": "Venice"},    # Flight day (departure)
        {"day_range": "Day 6", "place": "Madrid"},    # Flight day (arrival)
        {"day_range": "Day 6-11", "place": "Madrid"},
        {"day_range": "Day 11", "place": "Madrid"},   # Flight day (departure)
        {"day_range": "Day 11", "place": "Santorini"},# Flight day (arrival)
        {"day_range": "Day 11-14", "place": "Santorini"},
        {"day_range": "Day 14", "place": "Santorini"},# Flight day (departure)
        {"day_range": "Day 14", "place": "London"},   # Flight day (arrival)
        {"day_range": "Day 14-17", "place": "London"},
        {"day_range": "Day 17", "place": "London"},   # Flight day (departure)
        {"day_range": "Day 17", "place": "Lisbon"},   # Flight day (arrival)
        {"day_range": "Day 17", "place": "Lisbon"}    # Single day stay
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()