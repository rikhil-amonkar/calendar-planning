def main():
    itinerary = [
        {"day_range": "Day 1-3", "place": "Copenhagen"},
        {"day_range": "Day 3", "place": "Copenhagen"},
        {"day_range": "Day 3", "place": "Tallinn"},
        {"day_range": "Day 3-6", "place": "Tallinn"},
        {"day_range": "Day 6", "place": "Tallinn"},
        {"day_range": "Day 6", "place": "London"},
        {"day_range": "Day 6-10", "place": "London"},
        {"day_range": "Day 10", "place": "London"},
        {"day_range": "Day 10", "place": "Oslo"},
        {"day_range": "Day 10-14", "place": "Oslo"},
        {"day_range": "Day 14", "place": "Oslo"},
        {"day_range": "Day 14", "place": "Mykonos"},
        {"day_range": "Day 14-16", "place": "Mykonos"},
        {"day_range": "Day 16", "place": "Mykonos"},
        {"day_range": "Day 16", "place": "Nice"}
    ]
    print({"itinerary": itinerary})

if __name__ == '__main__':
    main()