def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Brussels"},
        {"day_range": "Day 2", "place": "Brussels"},
        {"day_range": "Day 2", "place": "Reykjavik"},
        {"day_range": "Day 2-5", "place": "Reykjavik"},
        {"day_range": "Day 5", "place": "Reykjavik"},
        {"day_range": "Day 5", "place": "Madrid"},
        {"day_range": "Day 5-8", "place": "Madrid"},
        {"day_range": "Day 8", "place": "Madrid"},
        {"day_range": "Day 8", "place": "Venice"},
        {"day_range": "Day 8-11", "place": "Venice"},
        {"day_range": "Day 11", "place": "Venice"},
        {"day_range": "Day 11", "place": "London"},
        {"day_range": "Day 11-14", "place": "London"},
        {"day_range": "Day 14", "place": "London"},
        {"day_range": "Day 14", "place": "Santorini"},
        {"day_range": "Day 14-17", "place": "Santorini"},
        {"day_range": "Day 17", "place": "Santorini"}
    ]
    result = {"itinerary": itinerary}
    print(result)

if __name__ == "__main__":
    main()