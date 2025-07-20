def main():
    itinerary = [
        {"day_range": "Day 0", "place": "Brussels"},
        {"day_range": "Day 2-3", "place": "Reykjavik"},
        {"day_range": "Day 5", "place": "Santorini"},
        {"day_range": "Day 7", "place": "Lisbon"},
        {"day_range": "Day 9", "place": "Venice"},
        {"day_range": "Day 11-14", "place": "Madrid"},
        {"day_range": "Day 16", "place": "London"}
    ]
    result = {
        "itinerary": itinerary
    }
    print(result)

if __name__ == "__main__":
    main()