def main():
    itinerary = [
        {"day_range": "Day 1", "place": "Amsterdam"},
        {"day_range": "Day 2-4", "place": "Bucharest"},
        {"day_range": "Day 5", "place": "Riga"},
        {"day_range": "Day 6-10", "place": "Vilnius"},
        {"day_range": "Day 11-12", "place": "Frankfurt"},
        {"day_range": "Day 13", "place": "London"},
        {"day_range": "Day 14-15", "place": "Stockholm"}
    ]
    result = {"itinerary": itinerary}
    print(result)

if __name__ == "__main__":
    main()