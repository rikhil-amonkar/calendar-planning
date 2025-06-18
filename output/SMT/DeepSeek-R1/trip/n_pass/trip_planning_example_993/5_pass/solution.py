def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Amsterdam"},
        {"day_range": "Day 2-5", "place": "Bucharest"},
        {"day_range": "Day 6", "place": "Riga"},
        {"day_range": "Day 6-10", "place": "Vilnius"},
        {"day_range": "Day 10-12", "place": "Frankfurt"},
        {"day_range": "Day 12", "place": "London"},
        {"day_range": "Day 12-15", "place": "Stockholm"}
    ]
    result = {"itinerary": itinerary}
    print(result)

if __name__ == "__main__":
    main()