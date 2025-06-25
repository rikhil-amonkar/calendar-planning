def main():
    itinerary = [
        {"day_range": "Day 1", "place": "Stuttgart"},
        {"day_range": "Day 2-6", "place": "Venice"},
        {"day_range": "Day 7-9", "place": "Barcelona"},
        {"day_range": "Day 10-12", "place": "Florence"},
        {"day_range": "Day 13", "place": "Stockholm"},
        {"day_range": "Day 14-15", "place": "Frankfurt"},
        {"day_range": "Day 16-17", "place": "Salzburg"},
        {"day_range": "Day 18", "place": "Stuttgart"}
    ]
    result = {"itinerary": itinerary}
    print(result)

if __name__ == "__main__":
    main()