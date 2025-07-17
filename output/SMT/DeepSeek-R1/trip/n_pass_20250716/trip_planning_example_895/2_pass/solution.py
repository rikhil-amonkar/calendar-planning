def main():
    itinerary = [
        {"day_range": "Day 0-2", "place": "Brussels"},
        {"day_range": "Day 3", "place": "Reykjavik"},
        {"day_range": "Day 4", "place": "Reykjavik"},
        {"day_range": "Day 4", "place": "Venice"},
        {"day_range": "Day 5-7", "place": "Venice"},
        {"day_range": "Day 8", "place": "Venice"},
        {"day_range": "Day 8", "place": "Lisbon"},
        {"day_range": "Day 8-11", "place": "Lisbon"},
        {"day_range": "Day 12", "place": "Lisbon"},
        {"day_range": "Day 12", "place": "Madrid"},
        {"day_range": "Day 12-16", "place": "Madrid"},
        {"day_range": "Day 16", "place": "Madrid"},
        {"day_range": "Day 16", "place": "Santorini"},
        {"day_range": "Day 16-17", "place": "Santorini"},
        {"day_range": "Day 17", "place": "Santorini"},
        {"day_range": "Day 17", "place": "London"}
    ]

    result = {
        "itinerary": itinerary
    }
    print(result)

if __name__ == "__main__":
    main()