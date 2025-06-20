def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Vienna"},
        {"day_range": "Day 5", "place": "Vienna"},
        {"day_range": "Day 5", "place": "Prague"},
        {"day_range": "Day 5-9", "place": "Prague"},
        {"day_range": "Day 9", "place": "Prague"},
        {"day_range": "Day 9", "place": "Split"},
        {"day_range": "Day 9-13", "place": "Split"},
        {"day_range": "Day 13", "place": "Split"},
        {"day_range": "Day 13", "place": "Amsterdam"},
        {"day_range": "Day 13-15", "place": "Amsterdam"},
        {"day_range": "Day 15", "place": "Amsterdam"},
        {"day_range": "Day 15", "place": "Riga"},
        {"day_range": "Day 15-16", "place": "Riga"},
        {"day_range": "Day 16", "place": "Riga"},
        {"day_range": "Day 16", "place": "Stockholm"},
        {"day_range": "Day 16-17", "place": "Stockholm"},
        {"day_range": "Day 17", "place": "Stockholm"},
        {"day_range": "Day 17", "place": "Brussels"},
        {"day_range": "Day 17-20", "place": "Brussels"},
        {"day_range": "Day 20", "place": "Brussels"},
        {"day_range": "Day 20", "place": "Seville"}
    ]
    print(f'{{"itinerary": {itinerary}}}')

if __name__ == "__main__":
    main()