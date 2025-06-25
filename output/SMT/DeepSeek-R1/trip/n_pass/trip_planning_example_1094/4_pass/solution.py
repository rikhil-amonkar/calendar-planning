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
        {"day_range": "Day 11-15", "place": "Edinburgh"},  # Covers Edinburgh event days 12-15
        {"day_range": "Day 15", "place": "Edinburgh"},
        {"day_range": "Day 15", "place": "Barcelona"},     # Travel to Barcelona on day 15
        {"day_range": "Day 16", "place": "Barcelona"},     # Barcelona event (day 16 beyond trip)
        {"day_range": "Day 16", "place": "Stockholm"},     # Travel to Stockholm on day 16
        {"day_range": "Day 17", "place": "Stockholm"}      # Stockholm event (day 17 beyond trip)
    ]
    result = {'itinerary': itinerary}
    print(result)

if __name__ == '__main__':
    main()