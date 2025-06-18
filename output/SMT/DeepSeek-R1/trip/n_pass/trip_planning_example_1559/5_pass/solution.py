def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Tallinn"},
        {"day_range": "Day 2", "place": "Tallinn"},
        {"day_range": "Day 2", "place": "Prague"},
        {"day_range": "Day 2-3", "place": "Prague"},
        {"day_range": "Day 3", "place": "Prague"},
        {"day_range": "Day 3", "place": "Valencia"},
        {"day_range": "Day 3-4", "place": "Valencia"},
        {"day_range": "Day 4", "place": "Valencia"},
        {"day_range": "Day 4", "place": "Seville"},
        {"day_range": "Day 4-8", "place": "Seville"},
        {"day_range": "Day 8", "place": "Seville"},
        {"day_range": "Day 8", "place": "Paris"},
        {"day_range": "Day 8-12", "place": "Paris"},
        {"day_range": "Day 12", "place": "Paris"},
        {"day_range": "Day 12", "place": "Lyon"},
        {"day_range": "Day 12-13", "place": "Lyon"},
        {"day_range": "Day 13", "place": "Lyon"},
        {"day_range": "Day 13", "place": "Oslo"},
        {"day_range": "Day 13-16", "place": "Oslo"},
        {"day_range": "Day 16", "place": "Oslo"},
        {"day_range": "Day 16", "place": "Lisbon"},
        {"day_range": "Day 16-17", "place": "Lisbon"},
        {"day_range": "Day 17", "place": "Lisbon"},
        {"day_range": "Day 17", "place": "Nice"},
        {"day_range": "Day 17-21", "place": "Nice"},
        {"day_range": "Day 21", "place": "Nice"},
        {"day_range": "Day 21", "place": "Mykonos"},
        {"day_range": "Day 21-25", "place": "Mykonos"}
    ]
    print(f'{{"itinerary": {itinerary}}}')

if __name__ == "__main__":
    main()