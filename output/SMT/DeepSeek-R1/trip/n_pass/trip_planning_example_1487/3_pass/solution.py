def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Santorini"},
        {"day_range": "Day 5", "place": "Santorini"},
        {"day_range": "Day 5", "place": "Geneva"},  # Added transit stop in Group 1 city
        {"day_range": "Day 5", "place": "Naples"},  # Proceed to Naples
        {"day_range": "Day 5-8", "place": "Naples"},
        {"day_range": "Day 8", "place": "Naples"},
        {"day_range": "Day 8", "place": "Athens"},
        {"day_range": "Day 8-11", "place": "Athens"},
        {"day_range": "Day 11", "place": "Athens"},
        {"day_range": "Day 11", "place": "Copenhagen"},
        {"day_range": "Day 11-15", "place": "Copenhagen"},
        {"day_range": "Day 15", "place": "Copenhagen"},
        {"day_range": "Day 15", "place": "Dubrovnik"},
        {"day_range": "Day 15-17", "place": "Dubrovnik"},
        {"day_range": "Day 17", "place": "Dubrovnik"},
        {"day_range": "Day 17", "place": "Munich"},
        {"day_range": "Day 17-21", "place": "Munich"},
        {"day_range": "Day 21", "place": "Munich"},
        {"day_range": "Day 21", "place": "Brussels"},
        {"day_range": "Day 21-24", "place": "Brussels"},
        {"day_range": "Day 24", "place": "Brussels"},
        {"day_range": "Day 24", "place": "Prague"},
        {"day_range": "Day 24-25", "place": "Prague"},
        {"day_range": "Day 25", "place": "Prague"},
        {"day_range": "Day 25", "place": "Geneva"},  # Planned visit to Geneva
        {"day_range": "Day 25-27", "place": "Geneva"},
        {"day_range": "Day 27", "place": "Geneva"},
        {"day_range": "Day 27", "place": "Mykonos"},
        {"day_range": "Day 27-28", "place": "Mykonos"}
    ]
    result = {"itinerary": itinerary}
    print(result)

if __name__ == '__main__':
    main()