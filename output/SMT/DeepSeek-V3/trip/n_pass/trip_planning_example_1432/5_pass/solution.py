import json

def main():
    itinerary = {
        "itinerary": [
            {"day_range": "Day 1-3", "place": "Stockholm"},
            {"day_range": "Day 3", "place": "Stockholm"},
            {"day_range": "Day 3", "place": "Amsterdam"},
            {"day_range": "Day 3-5", "place": "Amsterdam"},
            {"day_range": "Day 5", "place": "Amsterdam"},
            {"day_range": "Day 5", "place": "Valencia"},
            {"day_range": "Day 5-6", "place": "Valencia"},
            {"day_range": "Day 6", "place": "Valencia"},
            {"day_range": "Day 6", "place": "Vienna"},
            {"day_range": "Day 6-10", "place": "Vienna"},
            {"day_range": "Day 10", "place": "Vienna"},
            {"day_range": "Day 10", "place": "Bucharest"},
            {"day_range": "Day 10-13", "place": "Bucharest"},
            {"day_range": "Day 13", "place": "Bucharest"},
            {"day_range": "Day 13", "place": "Frankfurt"},
            {"day_range": "Day 13", "place": "Frankfurt"},
            {"day_range": "Day 13", "place": "Athens"},
            {"day_range": "Day 13-18", "place": "Athens"},
            {"day_range": "Day 18", "place": "Athens"},
            {"day_range": "Day 18", "place": "Riga"},
            {"day_range": "Day 18-20", "place": "Riga"},
            {"day_range": "Day 20", "place": "Riga"},
            {"day_range": "Day 20", "place": "Frankfurt"},
            {"day_range": "Day 20-24", "place": "Frankfurt"},
            {"day_range": "Day 24", "place": "Frankfurt"},
            {"day_range": "Day 24", "place": "Salzburg"},
            {"day_range": "Day 24-29", "place": "Salzburg"},
            {"day_range": "Day 29", "place": "Salzburg"},
            {"day_range": "Day 29", "place": "Vienna"},  # Fly to Vienna first
            {"day_range": "Day 29", "place": "Vienna"},
            {"day_range": "Day 29", "place": "Frankfurt"},  # Then fly to Frankfurt
            {"day_range": "Day 29", "place": "Frankfurt"},
            {"day_range": "Day 29", "place": "Reykjavik"}   # Finally fly to Reykjavik
        ]
    }
    
    print(json.dumps(itinerary))

if __name__ == "__main__":
    main()