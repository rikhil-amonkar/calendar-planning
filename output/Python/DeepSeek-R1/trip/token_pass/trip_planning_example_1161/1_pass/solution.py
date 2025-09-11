def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Oslo"},
        {"day_range": "Day 2-4", "place": "Dubrovnik"},
        {"day_range": "Day 4-5", "place": "Helsinki"},
        {"day_range": "Day 5-6", "place": "Vilnius"},
        {"day_range": "Day 6-7", "place": "Krakow"},
        {"day_range": "Day 7-12", "place": "Paris"},
        {"day_range": "Day 12-15", "place": "Madrid"},
        {"day_range": "Day 15-18", "place": "Mykonos"}
    ]
    
    print(f'{{"itinerary": {itinerary}}}')

if __name__ == "__main__":
    main()