def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Paris"},
        {"day_range": "Day 2", "place": "Paris"},
        {"day_range": "Day 2", "place": "Krakow"},
        {"day_range": "Day 2-4", "place": "Krakow"},
        {"day_range": "Day 4", "place": "Krakow"},
        {"day_range": "Day 4", "place": "Vienna"},
        {"day_range": "Day 4-7", "place": "Vienna"},
        {"day_range": "Day 7", "place": "Vienna"},
        {"day_range": "Day 7", "place": "Riga"},
        {"day_range": "Day 7-10", "place": "Riga"},
        {"day_range": "Day 10", "place": "Riga"},
        {"day_range": "Day 10", "place": "Hamburg"},
        {"day_range": "Day 10-11", "place": "Hamburg"},
        {"day_range": "Day 11", "place": "Hamburg"},
        {"day_range": "Day 11", "place": "Edinburgh"},
        {"day_range": "Day 11-14", "place": "Edinburgh"},  # Adjusted to end on day 14
        {"day_range": "Day 14", "place": "Edinburgh"},
        {"day_range": "Day 14", "place": "Stockholm"},  # Travel to Stockholm
        {"day_range": "Day 15-16", "place": "Stockholm"}  # Covers Stockholm event
    ]
    result = {'itinerary': itinerary}
    print(result)

if __name__ == '__main__':
    main()