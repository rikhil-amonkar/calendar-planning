def main():
    itinerary = [
        {"day_range": "Day 1-3", "place": "Copenhagen"},
        {"day_range": "Day 3", "place": "Copenhagen"},
        {"day_range": "Day 3", "place": "Copenhagen to Tallinn"},
        {"day_range": "Day 3-6", "place": "Tallinn"},
        {"day_range": "Day 6", "place": "Tallinn"},
        {"day_range": "Day 6", "place": "Tallinn to London"},
        {"day_range": "Day 6-10", "place": "London"},
        {"day_range": "Day 10", "place": "London"},
        {"day_range": "Day 10", "place": "London to Mykonos"},
        {"day_range": "Day 10-11", "place": "Mykonos"},
        {"day_range": "Day 11", "place": "Mykonos"},
        {"day_range": "Day 11", "place": "Mykonos to Oslo"},
        {"day_range": "Day 11-13", "place": "Oslo"},
        {"day_range": "Day 13", "place": "Oslo"},
        {"day_range": "Day 13", "place": "Oslo to London"},
        {"day_range": "Day 14", "place": "London"},
        {"day_range": "Day 14", "place": "London to Nice"},
        {"day_range": "Day 14-16", "place": "Nice"}
    ]
    print({"itinerary": itinerary})

if __name__ == '__main__':
    main()