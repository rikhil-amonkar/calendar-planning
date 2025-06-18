def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Tallinn"},
        {"day_range": "Day 2", "place": "Tallinn"},
        {"day_range": "Day 2", "place": "Prague"},
        {"day_range": "Day 2-4", "place": "Prague"},
        {"day_range": "Day 4", "place": "Prague"},
        {"day_range": "Day 4", "place": "Valencia"},
        {"day_range": "Day 4-6", "place": "Valencia"},  # Adjusted to cover event
        {"day_range": "Day 6", "place": "Valencia"},
        {"day_range": "Day 6", "place": "Seville"},
        {"day_range": "Day 6-10", "place": "Seville"},
        {"day_range": "Day 10", "place": "Seville"},
        {"day_range": "Day 10", "place": "Paris"},
        {"day_range": "Day 10-13", "place": "Paris"},
        {"day_range": "Day 13", "place": "Paris"},
        {"day_range": "Day 13", "place": "Lyon"},
        {"day_range": "Day 13-16", "place": "Lyon"},
        {"day_range": "Day 16", "place": "Lyon"},
        {"day_range": "Day 16", "place": "Oslo"},
        {"day_range": "Day 16-18", "place": "Oslo"},
        {"day_range": "Day 18", "place": "Oslo"},
        {"day_range": "Day 18", "place": "Lisbon"},
        {"day_range": "Day 18-19", "place": "Lisbon"},
        {"day_range": "Day 19", "place": "Lisbon"},
        {"day_range": "Day 19", "place": "Nice"},
        {"day_range": "Day 19-22", "place": "Nice"},
        {"day_range": "Day 22", "place": "Nice"},
        {"day_range": "Day 22", "place": "Mykonos"},
        {"day_range": "Day 22-26", "place": "Mykonos"}
    ]
    print(f'{{"itinerary": {itinerary}}}')

if __name__ == "__main__":
    main()